#!/bin/bash

# Toma で元の example がどのように動作するか確認する
# 手続きに成功する場合は、結果を out/ に保存する
# $TIMEOUT 秒以内に停止しない、またはエラーが発生した場合は、エラーを出力する

TIMEOUT=120

# 引数の確認
if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <ex_directory>"
    exit 1
fi

FROM_DIR=$1
TO_DIR=out

# ディレクトリの存在チェック
if [ ! -d "$FROM_DIR" ]; then
    echo "Source directory does not exist."
    exit 1
fi

# 出力ディレクトリの作成（存在しない場合）
mkdir -p "$TO_DIR"

echo "" > "$TO_DIR"/timeouts.txt

# ファイル変換関数
convert_files() {
    local source_dir=$1
    local target_dir=$2
    local has_trs_files=false

    for file in "$source_dir"/*; do
        if [ -d "$file" ]; then
            # 再帰的に処理する前に、.trs ファイルが存在するか確認
            if find "$file" -type f -name '*.trs' | read; then
                has_trs_files=true
                local subdir=$(basename "$file")
                local new_target_dir="$target_dir/$subdir"
                mkdir -p "$new_target_dir"
                convert_files "$file" "$new_target_dir"
            fi
        elif [ -f "$file" ] && [[ "$file" == *.trs ]]; then
            has_trs_files=true
            local filename=$(basename -- "$file")
            local base="${filename%.*}"
            # ファイル名が数字から始まる場合は、プレフィックスを追加
            if [[ $base =~ ^[0-9] ]]; then
                base="g_$base"
            fi
            # ファイル名にハイフンが含まれる場合はアンダースコアに変換
            base="${base//-/_}"
            timeout $TIMEOUT toma --completion-with-parsable-output "$file" > "$target_dir/$base.out"
            # branch for $?
            status=$?
            if [ $status -eq 124 ]; then
                echo "Timeout: $base"
                echo "$base" >> "$TO_DIR"/timeouts.txt
            elif [ $status -ne 0 ]; then
                echo "Error: $base"
            else 
                echo "Success: $base"
            fi
        fi
    done

    # このディレクトリに .trs ファイルが一つもない場合、作成したディレクトリを削除
    if [ "$has_trs_files" = false ] && [ "$target_dir" != "$TO_DIR" ]; then
        rmdir "$target_dir"
    fi
}

convert_files "$FROM_DIR" "$TO_DIR"
