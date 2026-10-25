/* See LICENSE file for copyright and license details. */
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <time.h>
#include <unistd.h>

#include <X11/Xlib.h>
#include <X11/Xatom.h>
#include <X11/Xproto.h>
#include <X11/Xutil.h>
#ifdef XINERAMA
#include <X11/extensions/Xinerama.h>
#endif
#include <X11/extensions/Xrender.h>
#include <X11/Xft/Xft.h>

#include "drw.h"
#include "util.h"

/* macros */
#define INTERSECT(x,y,w,h,r)  (MAX(0, MIN((x)+(w),(r).x_org+(r).width)  - MAX((x),(r).x_org)) \
                             * MAX(0, MIN((y)+(h),(r).y_org+(r).height) - MAX((y),(r).y_org)))
#define TEXTW(X)              (drw_fontset_getwidth(drw, (X)) + lrpad)
#define NUMBERSMAXDIGITS      100
#define NUMBERSBUFSIZE        (NUMBERSMAXDIGITS * 2) + 1

#define OPAQUE                0xffu

/* enums */
enum { SchemeNorm, SchemeSel, SchemeNormHighlight, SchemeSelHighlight,
       SchemeOut, SchemeCursor, SchemeLast }; /* color schemes */

struct item {
	char *text;
	struct item *left, *right;
	int out;
};

typedef struct {
	KeySym ksym;
	unsigned int state;
} Key;

static char numbers[NUMBERSBUFSIZE] = "";
static char text[BUFSIZ] = "";
static char *embed;
static int bh, mw, mh;
static int inputw = 0, promptw;
static int lrpad; /* sum of left and right padding */
static size_t cursor;
static struct item *items = NULL;
static struct item *matches, *matchend;
static struct item *prev, *curr, *next, *sel;
static int mon = -1, screen;
static unsigned int using_vi_mode = 0;

/* Optional title and asynchronous, text-only preview. */
static const char *title = NULL, *preview_command = NULL, *preview_title = NULL;
static unsigned int preview_size = 45;
static int password_mode = 0;
static struct item *preview_item = NULL;
static int preview_fd = -1;
static pid_t preview_pid = -1;
static time_t preview_start;
static char preview_output[8193];
static size_t preview_length;

static Atom clip, utf8;
static Display *dpy;
static Window root, parentwin, win;
static XIC xic;

static Drw *drw;
static Clr *scheme[SchemeLast];

#include "config.h"

static int useargb = 0;
static Visual *visual;
static int depth;
static Colormap cmap;

static char * cistrstr(const char *s, const char *sub);
static int (*fstrncmp)(const char *, const char *, size_t) = strncasecmp;
static char *(*fstrstr)(const char *, const char *) = cistrstr;
static void xinitvisual();

static void drawmenu(void);

/* Reap cancelled preview commands without ever blocking keyboard input. */
static void
preview_reap(int signal_number)
{
	int saved_errno = errno;

	(void)signal_number;
	while (waitpid(-1, NULL, WNOHANG) > 0)
		;
	errno = saved_errno;
}

static void
preview_stop(void)
{
	if (preview_fd >= 0) {
		close(preview_fd);
		preview_fd = -1;
	}
	if (preview_pid > 0) {
		if (waitpid(preview_pid, NULL, WNOHANG) == 0)
			kill(preview_pid, SIGKILL);
		preview_pid = -1;
	}
}

static void
preview_select(void)
{
	int fds[2], flags;
	pid_t pid;

	if (!preview_command || preview_item == sel)
		return;
	preview_stop();
	preview_item = sel;
	preview_length = 0;
	preview_output[0] = '\0';
	if (!sel || lines == 0)
		return;
	if (pipe(fds) == -1)
		return;
	pid = fork();
	if (pid == -1) {
		close(fds[0]);
		close(fds[1]);
		return;
	}
	if (pid == 0) {
		int nullfd;
		close(fds[0]);
		if (dup2(fds[1], STDOUT_FILENO) == -1)
			_exit(127);
		close(fds[1]);
		nullfd = open("/dev/null", O_WRONLY);
		if (nullfd >= 0) {
			dup2(nullfd, STDERR_FILENO);
			close(nullfd);
		}
		/* Pass the item as data, never through shell interpolation. */
		if (setenv("DMENU_ITEM", sel->text, 1) == -1)
			_exit(127);
		execlp(preview_command, preview_command, sel->text, (char *)NULL);
		_exit(127);
	}
	close(fds[1]);
	flags = fcntl(fds[0], F_GETFL, 0);
	if (flags == -1 || fcntl(fds[0], F_SETFL, flags | O_NONBLOCK) == -1) {
		close(fds[0]);
		if (waitpid(pid, NULL, WNOHANG) == 0)
			kill(pid, SIGKILL);
		return;
	}
	preview_fd = fds[0];
	preview_pid = pid;
	preview_start = time(NULL);
}

static void
preview_read(void)
{
	char buf[1024];
	ssize_t n;
	size_t count;
	int changed = 0;

	if (preview_fd < 0)
		return;
	for (;;) {
		n = read(preview_fd, buf, sizeof buf);
		if (n > 0) {
			count = MIN((size_t)n, sizeof preview_output - 1 - preview_length);
			memcpy(preview_output + preview_length, buf, count);
			preview_length += count;
			preview_output[preview_length] = '\0';
			changed = 1;
			if (preview_length == sizeof preview_output - 1) {
				preview_stop();
				break;
			}
		} else if (n == 0) {
			preview_stop();
			break;
		} else if (errno == EINTR) {
			continue;
		} else if (errno == EAGAIN || errno == EWOULDBLOCK) {
			break;
		} else {
			preview_stop();
			break;
		}
	}
	if (changed)
		drawmenu();
}

static void
drawpreview(int x, int y, int w, int h)
{
	const char *p, *end;
	char line[1024];
	size_t n;
	int row = y, pad = lrpad / 2;

	if (w <= 2 * pad || h <= 0)
		return;
	drw_setscheme(drw, scheme[SchemeSel]);
	drw_rect(drw, x, y, 1, h, 1, 0);
	if (preview_title && *preview_title) {
		drw_text(drw, x + 1, row, w - 1, bh, pad, preview_title, 0);
		row += bh;
	}
	drw_setscheme(drw, scheme[SchemeNorm]);
	for (p = preview_output; *p && row + bh <= y + h; p = (*end == '\n' ? end + 1 : end)) {
		end = strchr(p, '\n');
		if (!end)
			end = p + strlen(p);
		n = MIN((size_t)(end - p), sizeof line - 1);
		memcpy(line, p, n);
		line[n] = '\0';
		drw_text(drw, x + pad + 1, row, w - pad - 1, bh, pad, line, 0);
		row += bh;
	}
}

static unsigned int
textw_clamp(const char *str, unsigned int n)
{
	unsigned int w = drw_fontset_getwidth_clamp(drw, str, n) + lrpad;
	return MIN(w, n);
}

static void
appenditem(struct item *item, struct item **list, struct item **last)
{
	if (*last)
		(*last)->right = item;
	else
		*list = item;

	item->left = *last;
	item->right = NULL;
	*last = item;
}

static void
calcoffsets(void)
{
	int i, n;

	if (lines > 0)
		n = lines * bh;
	else
		n = mw - (promptw + inputw + TEXTW("<") + TEXTW(">") + TEXTW(numbers));
	/* calculate which items will begin the next page and previous page */
	for (i = 0, next = curr; next; next = next->right)
		if ((i += (lines > 0) ? bh : textw_clamp(next->text, n)) > n)
			break;
	for (i = 0, prev = curr; prev && prev->left; prev = prev->left)
		if ((i += (lines > 0) ? bh : textw_clamp(prev->left->text, n)) > n)
			break;
}

static int
max_textw(void)
{
	int len = 0;
	for (struct item *item = items; item && item->text; item++)
		len = MAX(TEXTW(item->text), len);
	return len;
}

static void
cleanup(void)
{
	size_t i;

	preview_stop();

	XUngrabKeyboard(dpy, CurrentTime);
	for (i = 0; i < SchemeLast; i++)
		free(scheme[i]);
	for (i = 0; items && items[i].text; ++i)
		free(items[i].text);
	free(items);
	drw_free(drw);
	XSync(dpy, False);
	XCloseDisplay(dpy);
}

static char *
cistrstr(const char *h, const char *n)
{
	size_t i;

	if (!n[0])
		return (char *)h;

	for (; *h; ++h) {
		for (i = 0; n[i] && tolower((unsigned char)n[i]) ==
		            tolower((unsigned char)h[i]); ++i)
			;
		if (n[i] == '\0')
			return (char *)h;
	}
	return NULL;
}

 
static void
drawhighlights(struct item *item, int x, int y, int maxw)
{
	int i, indent;
	char c, *highlight;

	if (!(strlen(item->text) && strlen(text)))
		return;

	drw_setscheme(drw, scheme[item == sel
	                   ? SchemeSelHighlight
	                   : SchemeNormHighlight]);
	for (i = 0, highlight = item->text; *highlight && text[i];) {
		if (!fstrncmp(highlight, &text[i], 1)) {
			/* get indentation */
			c = *highlight;
			*highlight = '\0';
			indent = TEXTW(item->text);
			*highlight = c;

			/* highlight character */
			c = highlight[1];
			highlight[1] = '\0';
			drw_text(
				drw,
				x + indent - (lrpad / 2.),
				y,
				MIN(maxw - indent, TEXTW(highlight) - lrpad),
				bh, 0, highlight, 0
			);
			highlight[1] = c;
			++i;
		}
		++highlight;
	}
}

static int
drawitem(struct item *item, int x, int y, int w)
{
	int r;
	if (item == sel)
		drw_setscheme(drw, scheme[SchemeSel]);
	else if (item->out)
		drw_setscheme(drw, scheme[SchemeOut]);
	else
		drw_setscheme(drw, scheme[SchemeNorm]);

	r = drw_text(drw, x, y, w, bh, lrpad / 2, item->text, 0);
	drawhighlights(item, x, y, w);
	return r;
}

static void
recalculatenumbers()
{
	unsigned int numer = 0, denom = 0;
	struct item *item;
	if (matchend) {
		numer++;
		for (item = matchend; item && item->left; item = item->left)
			numer++;
	}
	for (item = items; item && item->text; item++)
		denom++;
	snprintf(numbers, NUMBERSBUFSIZE, "%d/%d", numer, denom);
}

static void
drawmenu(void)
{
	unsigned int curpos;
	struct item *item;
	int x = 0, y = 0, fh = drw->fonts->h, w;
	char masked[sizeof text];
	const char *shown = text;
	size_t k;
	int titleh = title && *title ? bh : 0;
	int listwidth = (preview_command && lines > 0)
	              ? mw * (100 - preview_size) / 100 : mw;

	preview_select();

	/* Mask the input without altering the actual text or selection output. */
	if (password_mode) {
		for (k = 0; k < strlen(text); k++)
			masked[k] = '*';
		masked[k] = '\0';
		shown = masked;
	}

	drw_setscheme(drw, scheme[SchemeNorm]);
	drw_rect(drw, 0, 0, mw, mh, 1, 1);

	if (titleh) {
		drw_setscheme(drw, scheme[SchemeSel]);
		drw_text(drw, 0, 0, mw, bh, lrpad / 2, title, 0);
	}
	y = titleh;
	if (prompt && *prompt) {
		drw_setscheme(drw, scheme[SchemeSel]);
		x = drw_text(drw, x, y, promptw, bh, lrpad / 2, prompt, 0);
	}
	/* Draw input field, spanning the full width. */
	w = (lines > 0 || !matches) ? mw - x : inputw;
	drw_setscheme(drw, scheme[SchemeNorm]);
	drw_text(drw, x, y, w, bh, lrpad / 2, shown, 0);

	curpos = TEXTW(shown) - TEXTW(&shown[cursor]);
	curpos += lrpad / 2 - 1;
	if (using_vi_mode && text[0] != '\0') {
		drw_setscheme(drw, scheme[SchemeCursor]);
		char vi_char[] = {password_mode ? '*' : text[cursor], '\0'};
		drw_text(drw, x + curpos, y, TEXTW(vi_char) - lrpad, bh, 0, vi_char, 0);
	} else if (using_vi_mode) {
		drw_setscheme(drw, scheme[SchemeNorm]);
		drw_rect(drw, x + curpos, y + 2, lrpad / 2, bh - 4, 1, 0);
	} else if (curpos < w) {
		drw_setscheme(drw, scheme[SchemeNorm]);
		drw_rect(drw, x + curpos, y + 2 + (bh - fh) / 2, 2, fh - 4, 1, 0);
	}

	recalculatenumbers();

	if (lines > 0) {
		/* The preview gets its own columns alongside the vertical list. */
		for (item = curr; item != next; item = item->right) {
			y += bh;
			drawitem(item, preview_command ? 0 : x, y,
			         preview_command ? listwidth : mw - x);
		}
		if (preview_command)
			drawpreview(listwidth, titleh + bh, mw - listwidth, lines * bh);
	} else if (matches) {
		/* Keep horizontal menus unchanged. */
		x += inputw;
		w = TEXTW("<");
		if (curr->left) {
			drw_setscheme(drw, scheme[SchemeNorm]);
			drw_text(drw, x, titleh, w, bh, lrpad / 2, "<", 0);
		}
		x += w;
		for (item = curr; item != next; item = item->right)
			x = drawitem(item, x, titleh, textw_clamp(item->text, mw - x - TEXTW(">") - TEXTW(numbers)));
		if (next) {
			w = TEXTW(">");
			drw_setscheme(drw, scheme[SchemeNorm]);
			drw_text(drw, mw - w - TEXTW(numbers), titleh, w, bh, lrpad / 2, ">", 0);
		}
	}

	drw_setscheme(drw, scheme[SchemeNorm]);
	drw_text(drw, mw - TEXTW(numbers), titleh, TEXTW(numbers), bh, lrpad / 2, numbers, 0);
	drw_map(drw, win, 0, 0, mw, mh);
}

static void
grabfocus(void)
{
	struct timespec ts = { .tv_sec = 0, .tv_nsec = 10000000  };
	Window focuswin;
	int i, revertwin;

	for (i = 0; i < 100; ++i) {
		XGetInputFocus(dpy, &focuswin, &revertwin);
		if (focuswin == win)
			return;
		XSetInputFocus(dpy, win, RevertToParent, CurrentTime);
		nanosleep(&ts, NULL);
	}
	die("cannot grab focus");
}

static void
grabkeyboard(void)
{
	struct timespec ts = { .tv_sec = 0, .tv_nsec = 1000000  };
	int i;

	if (embed)
		return;
	/* try to grab keyboard, we may have to wait for another process to ungrab */
	for (i = 0; i < 1000; i++) {
		if (XGrabKeyboard(dpy, DefaultRootWindow(dpy), True, GrabModeAsync,
		                  GrabModeAsync, CurrentTime) == GrabSuccess)
			return;
		nanosleep(&ts, NULL);
	}
	die("cannot grab keyboard");
}

static void
match(void)
{
	static char **tokv = NULL;
	static int tokn = 0;

	char buf[sizeof text], *s;
	int i, tokc = 0;
	size_t len, textsize;
	struct item *item, *lprefix, *lsubstr, *prefixend, *substrend;

	strcpy(buf, text);
	/* separate input text into tokens to be matched individually */
	for (s = strtok(buf, " "); s; tokv[tokc - 1] = s, s = strtok(NULL, " "))
		if (++tokc > tokn && !(tokv = realloc(tokv, ++tokn * sizeof *tokv)))
			die("cannot realloc %zu bytes:", tokn * sizeof *tokv);
	len = tokc ? strlen(tokv[0]) : 0;

	matches = lprefix = lsubstr = matchend = prefixend = substrend = NULL;
	textsize = strlen(text) + 1;
	for (item = items; item && item->text; item++) {
		for (i = 0; i < tokc; i++)
			if (!fstrstr(item->text, tokv[i]))
				break;
		if (i != tokc) /* not all tokens match */
			continue;
		/* exact matches go first, then prefixes, then substrings */
		if (!tokc || !fstrncmp(text, item->text, textsize))
			appenditem(item, &matches, &matchend);
		else if (!fstrncmp(tokv[0], item->text, len))
			appenditem(item, &lprefix, &prefixend);
		else
			appenditem(item, &lsubstr, &substrend);
	}
	if (lprefix) {
		if (matches) {
			matchend->right = lprefix;
			lprefix->left = matchend;
		} else
			matches = lprefix;
		matchend = prefixend;
	}
	if (lsubstr) {
		if (matches) {
			matchend->right = lsubstr;
			lsubstr->left = matchend;
		} else
			matches = lsubstr;
		matchend = substrend;
	}
	curr = sel = matches;
	calcoffsets();
}

static void
insert(const char *str, ssize_t n)
{
	if (strlen(text) + n > sizeof text - 1)
		return;
	/* move existing text out of the way, insert new text, and update cursor */
	memmove(&text[cursor + n], &text[cursor], sizeof text - cursor - MAX(n, 0));
	if (n > 0)
		memcpy(&text[cursor], str, n);
	cursor += n;
	match();
}

static size_t
nextrune(int inc)
{
	ssize_t n;

	/* return location of next utf8 rune in the given direction (+1 or -1) */
	for (n = cursor + inc; n + inc >= 0 && (text[n] & 0xc0) == 0x80; n += inc)
		;
	return n;
}

static void
movewordedge(int dir)
{
	if (dir < 0) { /* move cursor to the start of the word*/
		while (cursor > 0 && strchr(worddelimiters, text[nextrune(-1)]))
			cursor = nextrune(-1);
		while (cursor > 0 && !strchr(worddelimiters, text[nextrune(-1)]))
			cursor = nextrune(-1);
	} else { /* move cursor to the end of the word */
		while (text[cursor] && strchr(worddelimiters, text[cursor]))
			cursor = nextrune(+1);
		while (text[cursor] && !strchr(worddelimiters, text[cursor]))
			cursor = nextrune(+1);
	}
}

static void
vi_keypress(KeySym ksym, const XKeyEvent *ev)
{
	static const size_t quit_len = LENGTH(quit_keys);
	if (ev->state & ControlMask) {
		switch(ksym) {
		/* movement */
		case XK_d: /* fallthrough */
			if (next) {
				sel = curr = next;
				calcoffsets();
				goto draw;
			} else
				ksym = XK_G;
			break;
		case XK_u:
			if (prev) {
				sel = curr = prev;
				calcoffsets();
				goto draw;
			} else
				ksym = XK_g;
			break;
		case XK_p: /* fallthrough */
		case XK_P: break;
		case XK_c:
			cleanup();
			exit(1);
		case XK_Return: /* fallthrough */
		case XK_KP_Enter: break;
		default: return;
		}
	}
	switch(ksym) {
	/* movement */
	case XK_0:
		cursor = 0;
		break;
	case XK_dollar:
		if (text[cursor + 1] != '\0') {
			cursor = strlen(text) - 1;
			break;
		}
		break;
	case XK_b:
		movewordedge(-1);
		break;
	case XK_e:
		cursor = nextrune(+1);
		movewordedge(+1);
		if (text[cursor] == '\0')
			--cursor;
		else
			cursor = nextrune(-1);
		break;
	case XK_g:
		if (sel == matches) {
			break;
		}
		sel = curr = matches;
		calcoffsets();
		break;
	case XK_G:
		if (next) {
			/* jump to end of list and position items in reverse */
			curr = matchend;
			calcoffsets();
			curr = prev;
			calcoffsets();
			while (next && (curr = curr->right))
				calcoffsets();
		}
		sel = matchend;
		break;
	case XK_h:
		if (cursor)
			cursor = nextrune(-1);
		break;
	case XK_j:
		if (sel && sel->right && (sel = sel->right) == next) {
			curr = next;
			calcoffsets();
		}
		break;
	case XK_k:
		if (sel && sel->left && (sel = sel->left)->right == curr) {
			curr = prev;
			calcoffsets();
		}
		break;
	case XK_l:
		if (text[cursor] != '\0' && text[cursor + 1] != '\0')
			cursor = nextrune(+1);
		else if (text[cursor] == '\0' && cursor)
			--cursor;
		break;
	case XK_w:
		movewordedge(+1);
		if (text[cursor] != '\0' && text[cursor + 1] != '\0')
			cursor = nextrune(+1);
		else if (cursor)
			--cursor;
		break;
	/* insertion */
	case XK_a:
		cursor = nextrune(+1);
		/* fallthrough */
	case XK_i:
		using_vi_mode = 0;
		break;
	case XK_A:
		if (text[cursor] != '\0')
			cursor = strlen(text);
		using_vi_mode = 0;
		break;
	case XK_I:
		cursor = using_vi_mode = 0;
		break;
	case XK_p:
		if (text[cursor] != '\0')
			cursor = nextrune(+1);
		XConvertSelection(dpy, (ev->state & ControlMask) ? clip : XA_PRIMARY,
							utf8, utf8, win, CurrentTime);
		return;
	case XK_P:
		XConvertSelection(dpy, (ev->state & ControlMask) ? clip : XA_PRIMARY,
							utf8, utf8, win, CurrentTime);
		return;
	/* deletion */
	case XK_D:
		text[cursor] = '\0';
		if (cursor)
			cursor = nextrune(-1);
		match();
		break;
	case XK_x:
		cursor = nextrune(+1);
		insert(NULL, nextrune(-1) - cursor);
		if (text[cursor] == '\0' && text[0] != '\0')
			--cursor;
		match();
		break;
	/* misc. */
	case XK_Return:
	case XK_KP_Enter:
		puts((sel && !(ev->state & ShiftMask)) ? sel->text : text);
		if (!(ev->state & ControlMask)) {
			cleanup();
			exit(0);
		}
		if (sel)
			sel->out = 1;
		break;
	case XK_Tab:
		if (!sel)
			return;
		strncpy(text, sel->text, sizeof text - 1);
		text[sizeof text - 1] = '\0';
		cursor = strlen(text) - 1;
		match();
		break;
	default:
		for (size_t i = 0; i < quit_len; ++i)
			if (quit_keys[i].ksym == ksym &&
				(quit_keys[i].state & ev->state) == quit_keys[i].state) {
				cleanup();
				exit(1);
			}
	}
draw:
	drawmenu();
}

static void
keypress(XKeyEvent *ev)
{
	char buf[64];
	int len;
	KeySym ksym = NoSymbol;
	Status status;

	len = XmbLookupString(xic, ev, buf, sizeof buf, &ksym, &status);
	switch (status) {
	default: /* XLookupNone, XBufferOverflow */
		return;
	case XLookupChars: /* composed string from input method */
		goto insert;
	case XLookupKeySym:
	case XLookupBoth: /* a KeySym and a string are returned: use keysym */
		break;
	}

	if (using_vi_mode) {
		vi_keypress(ksym, ev);
		return;
	} else if (vi_mode &&
			   (ksym == global_esc.ksym &&
				(ev->state & global_esc.state) == global_esc.state)) {
		using_vi_mode = 1;
		if (cursor)
			cursor = nextrune(-1);
		goto draw;
	}

	if (ev->state & ControlMask) {
		switch(ksym) {
		case XK_a: ksym = XK_Home;      break;
		case XK_b: ksym = XK_Left;      break;
		case XK_c: ksym = XK_Escape;    break;
		case XK_d: ksym = XK_Delete;    break;
		case XK_e: ksym = XK_End;       break;
		case XK_f: ksym = XK_Right;     break;
		case XK_g: ksym = XK_Escape;    break;
		case XK_h: ksym = XK_BackSpace; break;
		case XK_i: ksym = XK_Tab;       break;
		case XK_j: /* fallthrough */
		case XK_J: /* fallthrough */
		case XK_m: /* fallthrough */
		case XK_M: ksym = XK_Return; ev->state &= ~ControlMask; break;
		case XK_n: ksym = XK_Down;      break;
		case XK_p: ksym = XK_Up;        break;

		case XK_k: /* delete right */
			text[cursor] = '\0';
			match();
			break;
		case XK_u: /* delete left */
			insert(NULL, 0 - cursor);
			break;
		case XK_w: /* delete word */
			while (cursor > 0 && strchr(worddelimiters, text[nextrune(-1)]))
				insert(NULL, nextrune(-1) - cursor);
			while (cursor > 0 && !strchr(worddelimiters, text[nextrune(-1)]))
				insert(NULL, nextrune(-1) - cursor);
			break;
		case XK_y: /* paste selection */
		case XK_Y:
			XConvertSelection(dpy, (ev->state & ShiftMask) ? clip : XA_PRIMARY,
			                  utf8, utf8, win, CurrentTime);
			return;
		case XK_Left:
		case XK_KP_Left:
			movewordedge(-1);
			goto draw;
		case XK_Right:
		case XK_KP_Right:
			movewordedge(+1);
			goto draw;
		case XK_Return:
		case XK_KP_Enter:
			break;
		case XK_bracketleft:
			cleanup();
			exit(1);
		default:
			return;
		}
	} else if (ev->state & Mod1Mask) {
		switch(ksym) {
		case XK_b:
			movewordedge(-1);
			goto draw;
		case XK_f:
			movewordedge(+1);
			goto draw;
		case XK_g: ksym = XK_Home;  break;
		case XK_G: ksym = XK_End;   break;
		case XK_h: ksym = XK_Up;    break;
		case XK_j: ksym = XK_Next;  break;
		case XK_k: ksym = XK_Prior; break;
		case XK_l: ksym = XK_Down;  break;
		default:
			return;
		}
	}

	switch(ksym) {
	default:
insert:
		if (!iscntrl((unsigned char)*buf))
			insert(buf, len);
		break;
	case XK_Delete:
	case XK_KP_Delete:
		if (text[cursor] == '\0')
			return;
		cursor = nextrune(+1);
		/* fallthrough */
	case XK_BackSpace:
		if (cursor == 0)
			return;
		insert(NULL, nextrune(-1) - cursor);
		break;
	case XK_End:
	case XK_KP_End:
		if (text[cursor] != '\0') {
			cursor = strlen(text);
			break;
		}
		if (next) {
			/* jump to end of list and position items in reverse */
			curr = matchend;
			calcoffsets();
			curr = prev;
			calcoffsets();
			while (next && (curr = curr->right))
				calcoffsets();
		}
		sel = matchend;
		break;
	case XK_Escape:
		cleanup();
		exit(1);
	case XK_Home:
	case XK_KP_Home:
		if (sel == matches) {
			cursor = 0;
			break;
		}
		sel = curr = matches;
		calcoffsets();
		break;
	case XK_Left:
	case XK_KP_Left:
		if (cursor > 0 && (!sel || !sel->left || lines > 0)) {
			cursor = nextrune(-1);
			break;
		}
		if (lines > 0)
			return;
		/* fallthrough */
	case XK_Up:
	case XK_KP_Up:
		if (sel && sel->left && (sel = sel->left)->right == curr) {
			curr = prev;
			calcoffsets();
		}
		break;
	case XK_Next:
	case XK_KP_Next:
		if (!next)
			return;
		sel = curr = next;
		calcoffsets();
		break;
	case XK_Prior:
	case XK_KP_Prior:
		if (!prev)
			return;
		sel = curr = prev;
		calcoffsets();
		break;
	case XK_Return:
	case XK_KP_Enter:
		puts((sel && !(ev->state & ShiftMask)) ? sel->text : text);
		if (!(ev->state & ControlMask)) {
			cleanup();
			exit(0);
		}
		if (sel)
			sel->out = 1;
		break;
	case XK_Right:
	case XK_KP_Right:
		if (text[cursor] != '\0') {
			cursor = nextrune(+1);
			break;
		}
		if (lines > 0)
			return;
		/* fallthrough */
	case XK_Down:
	case XK_KP_Down:
		if (sel && sel->right && (sel = sel->right) == next) {
			curr = next;
			calcoffsets();
		}
		break;
	case XK_Tab:
		if (!sel)
			return;
		cursor = strnlen(sel->text, sizeof text - 1);
		memcpy(text, sel->text, cursor);
		text[cursor] = '\0';
		match();
		break;
	}

draw:
	drawmenu();
}

static void
paste(void)
{
	char *p, *q;
	int di;
	unsigned long dl;
	Atom da;

	/* we have been given the current selection, now insert it into input */
	if (XGetWindowProperty(dpy, win, utf8, 0, (sizeof text / 4) + 1, False,
	                   utf8, &da, &di, &dl, &dl, (unsigned char **)&p)
	    == Success && p) {
		insert(p, (q = strchr(p, '\n')) ? q - p : (ssize_t)strlen(p));
		XFree(p);
	}
	if (using_vi_mode && text[cursor] == '\0')
		--cursor;
	drawmenu();
}

static void
readstdin(void)
{
	char *line = NULL;
	size_t i, itemsiz = 0, linesiz = 0;
	ssize_t len;

	/* read each line from stdin and add it to the item list */
	for (i = 0; (len = getline(&line, &linesiz, stdin)) != -1; i++) {
		if (i + 1 >= itemsiz) {
			itemsiz += 256;
			if (!(items = realloc(items, itemsiz * sizeof(*items))))
				die("cannot realloc %zu bytes:", itemsiz * sizeof(*items));
		}
		if (line[len - 1] == '\n')
			line[len - 1] = '\0';
		if (!(items[i].text = strdup(line)))
			die("strdup:");

		items[i].out = 0;
	}
	free(line);
	if (items)
		items[i].text = NULL;
	lines = MIN(lines, i);
}

static void
run(void)
{
	XEvent ev;
	struct pollfd fds[2];
	int ready;

	for (;;) {
		/*
		 * Only poll while a preview command is running. Without previews
		 * retain dmenu's ordinary blocking X event loop.
		 */
		if (preview_fd >= 0 && !XPending(dpy)) {
			fds[0].fd = ConnectionNumber(dpy);
			fds[0].events = POLLIN;
			fds[1].fd = preview_fd;
			fds[1].events = POLLIN | POLLHUP;
			ready = poll(fds, 2, 100);
			if (ready < 0 && errno != EINTR)
				die("preview poll:");
			if (ready > 0 && (fds[1].revents & (POLLIN | POLLHUP | POLLERR | POLLNVAL)))
				preview_read();
			/* Time limit prevents a broken backend from lingering. */
			if (preview_fd >= 0 && time(NULL) - preview_start >= 3) {
				preview_stop();
				if (preview_length == 0) {
					strcpy(preview_output, "Preview timed out.");
					preview_length = strlen(preview_output);
				}
				drawmenu();
			}
			if (!XPending(dpy))
				continue;
		}
		XNextEvent(dpy, &ev);
		if (XFilterEvent(&ev, win))
			continue;
		switch(ev.type) {
		case DestroyNotify:
			if (ev.xdestroywindow.window != win)
				break;
			cleanup();
			exit(1);
		case Expose:
			if (ev.xexpose.count == 0)
				drw_map(drw, win, 0, 0, mw, mh);
			break;
		case FocusIn:
			/* regrab focus from parent window */
			if (ev.xfocus.window != win)
				grabfocus();
			break;
		case KeyPress:
			keypress(&ev.xkey);
			break;
		case SelectionNotify:
			if (ev.xselection.property == utf8)
				paste();
			break;
		case VisibilityNotify:
			if (ev.xvisibility.state != VisibilityUnobscured)
				XRaiseWindow(dpy, win);
			break;
		}
	}
}

static void
setup(void)
{
	int x, y, i, j;
	unsigned int du;
	XSetWindowAttributes swa;
	XIM xim;
	Window w, dw, *dws;
	XWindowAttributes wa;
	XClassHint ch = {"dmenu", "dmenu"};
#ifdef XINERAMA
	XineramaScreenInfo *info;
	Window pw;
	int a, di, n, area = 0;
#endif
	/* init appearance */
    i = 0;
	for (j = 0; j < SchemeLast; j++)
		scheme[j] = drw_scm_create(drw, colors[j], alphas[i], 2);

	clip = XInternAtom(dpy, "CLIPBOARD",   False);
	utf8 = XInternAtom(dpy, "UTF8_STRING", False);

	/* calculate menu geometry */
	bh = drw->fonts->h + 2;
	bh = MAX(bh,lineheight);	/* make a menu line AT LEAST 'lineheight' tall */
	lines = MAX(lines, 0);
	mh = (lines + 1 + (title && *title ? 1 : 0)) * bh;
	promptw = (prompt && *prompt) ? TEXTW(prompt) - lrpad / 4 : 0;
#ifdef XINERAMA
	i = 0;
	if (parentwin == root && (info = XineramaQueryScreens(dpy, &n))) {
		XGetInputFocus(dpy, &w, &di);
		if (mon >= 0 && mon < n)
			i = mon;
		else if (w != root && w != PointerRoot && w != None) {
			/* find top-level window containing current input focus */
			do {
				if (XQueryTree(dpy, (pw = w), &dw, &w, &dws, &du) && dws)
					XFree(dws);
			} while (w != root && w != pw);
			/* find xinerama screen with which the window intersects most */
			if (XGetWindowAttributes(dpy, pw, &wa))
				for (j = 0; j < n; j++)
					if ((a = INTERSECT(wa.x, wa.y, wa.width, wa.height, info[j])) > area) {
						area = a;
						i = j;
					}
		}
		/* no focused window is on screen, so use pointer location instead */
		if (mon < 0 && !area && XQueryPointer(dpy, root, &dw, &dw, &x, &y, &di, &di, &du))
			for (i = 0; i < n; i++)
				if (INTERSECT(x, y, 1, 1, info[i]) != 0)
					break;

		if (centered) {
			mw = MIN(MAX(max_textw() + promptw,
			            preview_command ? MAX(min_width, 900) : min_width), info[i].width);
			x = info[i].x_org + ((info[i].width  - mw) / 2);
			y = info[i].y_org + ((info[i].height - mh) / menu_height_ratio);
		} else {
			x = info[i].x_org;
			y = info[i].y_org + (topbar ? 0 : info[i].height - mh);
			mw = info[i].width;
		}

		XFree(info);
	} else
#endif
	{
		if (!XGetWindowAttributes(dpy, parentwin, &wa))
			die("could not get embedding window attributes: 0x%lx",
			    parentwin);

		if (centered) {
			mw = MIN(MAX(max_textw() + promptw,
			            preview_command ? MAX(min_width, 900) : min_width), wa.width);
			x = (wa.width  - mw) / 2;
			y = (wa.height - mh) / 2;
		} else {
			x = 0;
			y = topbar ? 0 : wa.height - mh;
			mw = wa.width;
		}
	}
	promptw = (prompt && *prompt) ? TEXTW(prompt) - lrpad / 4 : 0;
	inputw = mw / 3; /* input width: ~33% of monitor width */
	match();

	/* create menu window */
	swa.override_redirect = True;
	swa.background_pixel = 0;
	swa.border_pixel = 0;
	swa.colormap = cmap;
	swa.event_mask = ExposureMask | KeyPressMask | VisibilityChangeMask;
	win = XCreateWindow(dpy, root, x, y, mw, mh, border_width,
	                    depth, CopyFromParent, visual,
	                    CWOverrideRedirect | CWBackPixel | CWBorderPixel | CWColormap | CWEventMask, &swa);

	if (border_width)
		XSetWindowBorder(dpy, win, scheme[SchemeSel][ColBg].pixel);
	XSetClassHint(dpy, win, &ch);

	/* input methods */
	if ((xim = XOpenIM(dpy, NULL, NULL, NULL)) == NULL)
		die("XOpenIM failed: could not open input device");

	xic = XCreateIC(xim, XNInputStyle, XIMPreeditNothing | XIMStatusNothing,
	                XNClientWindow, win, XNFocusWindow, win, NULL);

	XMapRaised(dpy, win);
	if (embed) {
		XReparentWindow(dpy, win, parentwin, x, y);
		XSelectInput(dpy, parentwin, FocusChangeMask | SubstructureNotifyMask);
		if (XQueryTree(dpy, parentwin, &dw, &w, &dws, &du) && dws) {
			for (i = 0; i < du && dws[i] != win; ++i)
				XSelectInput(dpy, dws[i], FocusChangeMask);
			XFree(dws);
		}
		grabfocus();
	}
	drw_resize(drw, mw, mh);
	drawmenu();
}

static void
usage(void)
{
	die("usage: dmenu [-bcfivs] [-vi] [-password] [-l lines] [-h height] [-p prompt] [-fn font] [-m monitor]\n"
	    "             [-nb color] [-nf color] [-sb color] [-sf color] [-bw width]\n"
	    "             [-nhb color] [-nhf color] [-shb color] [-shf color] [-w windowid]\n"
	    "             [-title text] [-preview executable] [-preview-title text]\n"
	    "             [-preview-pos right] [-preview-size percent]");
}

int
main(int argc, char *argv[])
{
	XWindowAttributes wa;
	struct sigaction child_action;
	int i, fast = 0;

	memset(&child_action, 0, sizeof child_action);
	child_action.sa_handler = preview_reap;
	child_action.sa_flags = SA_RESTART | SA_NOCLDSTOP;
	sigemptyset(&child_action.sa_mask);
	if (sigaction(SIGCHLD, &child_action, NULL) == -1)
		die("sigaction:");

	for (i = 1; i < argc; i++)
		/* these options take no arguments */
		if (!strcmp(argv[i], "-v")) {      /* prints version information */
			puts("dmenu-"VERSION);
			exit(0);
		} else if (!strcmp(argv[i], "-b")) /* appears at the bottom of the screen */
			topbar = 0;
		else if (!strcmp(argv[i], "-f"))   /* grabs keyboard before reading stdin */
			fast = 1;
		else if (!strcmp(argv[i], "-c"))   /* centers dmenu on screen */
			centered = 1;
		else if (!strcmp(argv[i], "-password"))
			password_mode = 1;
		else if (!strcmp(argv[i], "-i")) { /* case-insensitive item matching */
			fstrncmp = strncasecmp;
			fstrstr = cistrstr;
		} else if (!strcmp(argv[i], "-s")) { /* case-sensitive item matching */
			fstrncmp = strncmp;
			fstrstr = strstr;
		} else if (!strcmp(argv[i], "-vi")) {
			vi_mode = 1;
			using_vi_mode = start_mode;
			global_esc.ksym = XK_Escape;
			global_esc.state = 0;
		} else if (i + 1 == argc)
			usage();
		/* these options take one argument */
		else if (!strcmp(argv[i], "-l"))   /* number of lines in vertical list */
			lines = atoi(argv[++i]);
		else if (!strcmp(argv[i], "-h")) { /* minimum height of one menu line */
			lineheight = atoi(argv[++i]);
			lineheight = MAX(lineheight, min_lineheight);
		}
		else if (!strcmp(argv[i], "-m"))
			mon = atoi(argv[++i]);
		else if (!strcmp(argv[i], "-p"))   /* adds prompt to left of input field */
			prompt = argv[++i];
		else if (!strcmp(argv[i], "-fn"))  /* font or font set */
			fonts[0] = argv[++i];
		else if (!strcmp(argv[i], "-nb"))  /* normal background color */
			colors[SchemeNorm][ColBg] = argv[++i];
		else if (!strcmp(argv[i], "-nf"))  /* normal foreground color */
			colors[SchemeNorm][ColFg] = argv[++i];
		else if (!strcmp(argv[i], "-sb"))  /* selected background color */
			colors[SchemeSel][ColBg] = argv[++i];
		else if (!strcmp(argv[i], "-sf"))  /* selected foreground color */
			colors[SchemeSel][ColFg] = argv[++i];
		else if (!strcmp(argv[i], "-nhb")) /* normal hi background color */
			colors[SchemeNormHighlight][ColBg] = argv[++i];
		else if (!strcmp(argv[i], "-nhf")) /* normal hi foreground color */
			colors[SchemeNormHighlight][ColFg] = argv[++i];
		else if (!strcmp(argv[i], "-shb")) /* selected hi background color */
			colors[SchemeSelHighlight][ColBg] = argv[++i];
		else if (!strcmp(argv[i], "-shf")) /* selected hi foreground color */
			colors[SchemeSelHighlight][ColFg] = argv[++i];
		else if (!strcmp(argv[i], "-w"))   /* embedding window id */
			embed = argv[++i];
		else if (!strcmp(argv[i], "-bw"))
			border_width = atoi(argv[++i]); /* border width */
		else if (!strcmp(argv[i], "-title"))
			title = argv[++i];
		else if (!strcmp(argv[i], "-preview"))
			preview_command = argv[++i];
		else if (!strcmp(argv[i], "-preview-title"))
			preview_title = argv[++i];
		else if (!strcmp(argv[i], "-preview-size")) {
			int parsed = atoi(argv[++i]);
			if (parsed < 20 || parsed > 70)
				usage();
			preview_size = parsed;
		} else if (!strcmp(argv[i], "-preview-pos")) {
			if (strcmp(argv[++i], "right"))
				usage();
		}
		else
			usage();

	/* A password prompt must never send the secret to an external preview. */
	if (password_mode && preview_command)
		usage();

	if (!setlocale(LC_CTYPE, "") || !XSupportsLocale())
		fputs("warning: no locale support\n", stderr);
	if (!(dpy = XOpenDisplay(NULL)))
		die("cannot open display");
	screen = DefaultScreen(dpy);
	root = RootWindow(dpy, screen);
	if (!embed || !(parentwin = strtol(embed, NULL, 0)))
		parentwin = root;
	if (!XGetWindowAttributes(dpy, parentwin, &wa))
		die("could not get embedding window attributes: 0x%lx",
		    parentwin);
	xinitvisual();
	drw = drw_create(dpy, screen, root, wa.width, wa.height, visual, depth, cmap);
	if (!drw_fontset_create(drw, fonts, LENGTH(fonts)))
		die("no fonts could be loaded.");
	lrpad = drw->fonts->h;

#ifdef __OpenBSD__
	if (pledge("stdio rpath", NULL) == -1)
		die("pledge");
#endif

	if (fast && !isatty(0)) {
		grabkeyboard();
		readstdin();
	} else {
		readstdin();
		grabkeyboard();
	}
	setup();
	run();

	return 1; /* unreachable */
}

void
xinitvisual()
{
	XVisualInfo *infos;
	XRenderPictFormat *fmt;
	int nitems;
	int i;
	XVisualInfo tpl = {
		.screen = screen,
		.depth = 32,
		.class = TrueColor
	};
	long masks = VisualScreenMask | VisualDepthMask | VisualClassMask;
	infos = XGetVisualInfo(dpy, masks, &tpl, &nitems);
	visual = NULL;
	for(i = 0; i < nitems; i ++) {
		fmt = XRenderFindVisualFormat(dpy, infos[i].visual);
		if (fmt->type == PictTypeDirect && fmt->direct.alphaMask) {
			 visual = infos[i].visual;
			 depth = infos[i].depth;
			 cmap = XCreateColormap(dpy, root, visual, AllocNone);
			 useargb = 1;
			 break;
		}
	}
	XFree(infos);
	if (! visual) {
		visual = DefaultVisual(dpy, screen);
		depth = DefaultDepth(dpy, screen);
		cmap = DefaultColormap(dpy, screen);
	}
}
