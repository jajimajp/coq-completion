#!/bin/bash

# 引数の確認
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <from_directory> <to_directory>"
    exit 1
fi

FROM_DIR=$1
TO_DIR=$2

# ディレクトリの存在チェック
if [ ! -d "$FROM_DIR" ]; then
    echo "Source directory does not exist."
    exit 1
fi

# 出力ディレクトリの作成（存在しない場合）
mkdir -p "$TO_DIR"

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
            ./bin/a.out "$file" > "$target_dir/$base.v"
        fi
    done

    # このディレクトリに .trs ファイルが一つもない場合、作成したディレクトリを削除
    if [ "$has_trs_files" = false ] && [ "$target_dir" != "$TO_DIR" ]; then
        rmdir "$target_dir"
    fi
}

convert_files "$FROM_DIR" "$TO_DIR"