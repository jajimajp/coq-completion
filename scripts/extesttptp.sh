#!/bin/bash

TIMEOUT=20

# ヘッダーを出力
echo "# Examples"
echo ""
echo "Examples in this directory are auto-generated by converting examples in TPTP."
echo ""
echo "Each example is tested with a timeout of $TIMEOUT seconds."
echo "- 🟢 OK: Compilation completed successfully."
echo "- 🔴 FAIL: Runtime error."
echo "- 🟡 TIMEOUT: timeout ($TIMEOUT s)."
echo ""
echo "## Results"
echo ""
echo "| File | LPO.v | Hammer.v | SMT.v |"
echo "|---|---|---|---|"

# ファイルごとに結果を表示する関数
process_file() {
    local file="$1"
    local result
    # 結果を出力
    # Check if the result directory exists, if not, create it
    if [ ! -d "../result" ]; then
        mkdir -p ../result
    fi

    # Check if the directory for the problem name exists in ./result, if not, create it
    local problem_dir="../result/$(basename "$dir")"
    if [ ! -d "$problem_dir" ]; then
        mkdir -p "$problem_dir"
    fi
    local output_file="$(basename "$file" .v).out"
    if timeout $TIMEOUT coqc "$file" > "$problem_dir/$output_file" 2>&1; then
        result="🟢 OK"
    else
        if [ $? -eq 124 ]; then
            result="🟡 TIMEOUT"
        else
            result="🔴 FAIL"
        fi
    fi

    echo "$result [out]($problem_dir/$output_file)"
}

# 現在のディレクトリから再帰的にディレクトリを検索して処理
find . -type d | while read -r dir; do
    compllpo_file="$dir/LPO.v"
    ham_file="$dir/Hammer.v"
    smt_file="$dir/SMT.v"

    if [ -f "$ham_file" ] || [ -f "$compllpo_file" ] || [ -f "$smt_file" ]; then
        echo -n "| [$dir]($dir) |"

        if [ -f "$compllpo_file" ]; then
            echo -n " $(process_file "$compllpo_file") |"
        else
            echo -n " N/A |"
        fi

        if [ -f "$ham_file" ]; then
            echo -n " $(process_file "$ham_file") |"
        else
            echo -n " N/A |"
        fi

        if [ -f "$smt_file" ]; then
            echo -n " $(process_file "$smt_file") |"
        else
            echo -n " N/A |"
        fi

        echo ""
    fi
done
