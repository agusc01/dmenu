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

if output=$(printf 'Home Wi-Fi\n' | DISPLAY= ./dmenu --not-an-option 2>&1); then
    echo 'Error: dmenu accepted an unknown option.' >&2
    exit 1
fi
case "$output" in
    *'usage: dmenu'*) ;;
    *) echo 'Error: Invalid options must display usage.' >&2; exit 1 ;;
esac

echo 'dmenu CLI option tests passed.'
