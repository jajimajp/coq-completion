#!/bin/bash

TIMEOUT=20

# ヘッダーを出力
echo "# Examples"
echo ""
echo "Examples in this directory are auto-generated by converting examples in Toma repository."
echo ""
echo "Each example is tested with a timeout of $TIMEOUT seconds."
echo "- 🟢 OK: Compilation completed successfully."
echo "- 🔴 FAIL: Runtime error."
echo "- 🟡 TIMEOUT: timeout ($TIMEOUT s)."
echo ""
echo "## Results"
echo ""
echo "| File | Compl.v | Ham.v | ComplLPO.v |"
echo "|---|---|---|---|"

# ファイルごとに結果を表示する関数
process_file() {
    local file="$1"
    local result

    if timeout $TIMEOUT coqc "$file" > /dev/null 2>&1; then
        result="🟢 OK"
    else
        if [ $? -eq 124 ]; then
            result="🟡 TIMEOUT"
        else
            result="🔴 FAIL"
        fi
    fi

    echo "$result"
}

# 現在のディレクトリから再帰的にディレクトリを検索して処理
find . -type d | while read -r dir; do
    compl_file="$dir/Compl.v"
    ham_file="$dir/Ham.v"
    compllpo_file="$dir/ComplLPO.v"

    if [ -f "$compl_file" ] || [ -f "$ham_file" ] || [ -f "$compllpo_file" ]; then
        echo -n "| [$dir]($dir) |"

        if [ -f "$compl_file" ]; then
            echo -n " $(process_file "$compl_file") |"
        else
            echo -n " N/A |"
        fi

        if [ -f "$ham_file" ]; then
            echo -n " $(process_file "$ham_file") |"
        else
            echo -n " N/A |"
        fi

        if [ -f "$compllpo_file" ]; then
            echo -n " $(process_file "$compllpo_file") |"
        else
            echo -n " N/A |"
        fi

        echo ""
    fi
done
