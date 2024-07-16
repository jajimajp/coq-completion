require 'fileutils'

# 出力ディレクトリの作成
output_dir = '../gen_all'
FileUtils.mkdir_p(output_dir)

# 再帰的にディレクトリを探索し、*.p ファイルを処理
def process_directory(base_directory, current_directory, output_dir)
  Dir.foreach(current_directory) do |entry|
    next if entry == '.' || entry == '..'

    path = File.join(current_directory, entry)

    if File.directory?(path)
      # ディレクトリの場合、再帰的に処理
      process_directory(base_directory, path, output_dir)
    elsif File.file?(path) && File.extname(path) == '.p'
      # .p ファイルの場合、tptp2coqp を実行して出力をリダイレクト
      relative_path = path.sub(base_directory + '/', '')
      relative_dir = File.join(output_dir, relative_path.sub(/\.p$/, ''))
      FileUtils.mkdir_p(relative_dir)

      # `tptp2coqp file.p` の結果を file/Compl.v に保存
      compl_output = `tptp2coqp "#{path}"`
      File.write(File.join(relative_dir, 'Compl.v'), compl_output)

      # `tptp2coqp file.p h` の結果を file/Ham.v に保存
      ham_output = `tptp2coqp "#{path}" h`
      File.write(File.join(relative_dir, 'Ham.v'), ham_output)

      # `tptp2coqp file.p l` の結果を file/ComplLPO.v に保存
      compl_lpo_output = `tptp2coqp "#{path}" l`
      File.write(File.join(relative_dir, 'ComplLPO.v'), compl_lpo_output)

      # `tptp2coqp file.p s` の結果を file/Smt.v に保存
      smt_output = `dune exec tptp2coqp "#{path}" s | sed -e 's/G/Z/g' -e 's/=/=?/g'`
      File.write(File.join(relative_dir, 'Smt.v'), smt_output)
    end
  end
end

# カレントディレクトリを処理
base_directory = Dir.pwd
process_directory(base_directory, base_directory, output_dir)
