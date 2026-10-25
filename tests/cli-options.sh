#!/bin/sh
set -eu

# CLI option regression test; requires build dependencies, not a running X server.
root=$(CDPATH= cd "$(dirname "$0")/.." && pwd)
cd "$root"
make dmenu

check_option() {
    if output=$(printf 'Home Wi-Fi\nGuest\n' | DISPLAY= ./dmenu "$@" 2>&1); then
        echo 'Error: dmenu unexpectedly started without an X display.' >&2
        exit 1
    fi
    case "$output" in
        *'cannot open display'*) ;;
        *)
            printf 'Error: dmenu rejected a supported option: %s\n%s\n' "$*" "$output" >&2
            exit 1
            ;;
    esac
}

# -i was listed in both the help and manual, but was not recognized.
check_option -i -c -l 10 -p 'Wi-Fi'
check_option -s -i -l 5
check_option -i -s -l 5


# Optional title and preview flags must parse without a live X server.
check_option -title 'Wi-Fi Networks' -l 10
check_option -i -c -l 10 -p Search \
    -title 'Wi-Fi Networks' \
    -preview wifi_info \
    -preview-title 'Network details' \
    -preview-pos right -preview-size 45

check_invalid() {
    if output=$(printf 'Home Wi-Fi\n' | DISPLAY= ./dmenu "$@" 2>&1); then
        echo 'Error: dmenu accepted an invalid option.' >&2
        exit 1
    fi
    case "$output" in
        *'usage: dmenu'*) ;;
        *)
            printf 'Error: Expected usage for invalid options: %s\n%s\n' "$*" "$output" >&2
            exit 1
            ;;
    esac
}

check_invalid -preview-size 0
check_invalid -preview-size 90
check_invalid -preview-pos bottom


# Masked text input must parse without requiring any graphical backend.
check_option -password -title 'Wi-Fi password' -p Password
check_invalid -password -preview printf
if output=$(printf 'Home Wi-Fi\n' | DISPLAY= ./dmenu --not-an-option 2>&1); then
    echo 'Error: dmenu accepted an unknown option.' >&2
    exit 1
fi
case "$output" in
    *'usage: dmenu'*) ;;
    *) echo 'Error: Invalid options must display usage.' >&2; exit 1 ;;
esac

echo 'dmenu CLI option tests passed.'
