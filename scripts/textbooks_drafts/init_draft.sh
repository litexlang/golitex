#!/bin/sh

set -eu

if [ "$#" -ne 1 ]; then
    echo "usage: scripts/textbooks_drafts/init_draft.sh <Book>" >&2
    exit 2
fi

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
book_name=$1
published_dir="$repository_root/textbooks/$book_name"
draft_dir="$repository_root/scripts/textbooks_drafts/$book_name"

case "$book_name" in
    ""|"."|".."|*/*)
        echo "invalid book name: $book_name" >&2
        exit 2
        ;;
esac

if [ ! -d "$published_dir" ]; then
    echo "published textbook does not exist: textbooks/$book_name" >&2
    exit 1
fi

if [ -e "$draft_dir" ]; then
    echo "draft already exists; refusing to overwrite: scripts/textbooks_drafts/$book_name" >&2
    exit 1
fi

cp -R "$published_dir" "$draft_dir"
echo "created scripts/textbooks_drafts/$book_name"
