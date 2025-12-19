#!/bin/bash

# Git Commit Message Helper Script
# This script helps create standardized commit messages following conventional commits format

echo "=========================================="
echo "Git Commit Message Helper"
echo "=========================================="
echo ""

# Step 1: Select commit type
echo "Please select a commit type:"
echo "1) developing new feature - 正在开发新功能"
echo "2) updating feature - 强化功能"
echo "3) deleting feature - 删除功能"
echo "4) fixing bug - 修补bug"
echo "5) documenting - 文档"
echo "6) refactoring - 重构"
echo "7) testing - 增加测试"
echo "8) chore - 构建过程或辅助工具的变动"
read -p "Enter your choice (1-8): " choice

case $choice in
    1)
        type="feat"
        ;;
    2)
        type="fix"
        ;;
    3)
        type="docs"
        ;;
    4)
        type="style"
        ;;
    5)
        type="refactor"
        ;;
    6)
        type="test"
        ;;
    7)
        type="chore"
        ;;
    *)
        echo "Invalid choice. Exiting."
        exit 1
        ;;
esac

echo ""
echo "Selected type: $type"
echo ""

# Step 2: Enter subject
read -p "Enter commit subject (max 80 characters): " subject

# Validate subject length
if [ ${#subject} -gt 80 ]; then
    echo "Warning: Subject exceeds 80 characters (${#subject} chars). Please keep it concise."
    read -p "Continue anyway? (y/n): " confirm
    if [ "$confirm" != "y" ] && [ "$confirm" != "Y" ]; then
        echo "Commit cancelled."
        exit 1
    fi
fi

# Step 3: Enter body (optional)
echo ""
read -p "Do you want to add a detailed body? (y/n): " add_body
body=""
if [ "$add_body" = "y" ] || [ "$add_body" = "Y" ]; then
    echo "Enter commit body (press Enter on an empty line to finish):"
    echo "(You can type multiple lines. Leave a line empty and press Enter to finish)"
    while IFS= read -r line; do
        if [ -z "$line" ] && [ -n "$body" ]; then
            # Empty line after content, finish
            break
        fi
        if [ -z "$line" ] && [ -z "$body" ]; then
            # First line is empty, skip body
            break
        fi
        if [ -n "$body" ]; then
            body="$body\n$line"
        else
            body="$line"
        fi
    done
fi

# Construct commit message
if [ -n "$body" ]; then
    commit_message="$type: $subject\n\n$body"
else
    commit_message="$type: $subject"
fi

# Execute git commit
git add .

git commit -m "$commit_message"