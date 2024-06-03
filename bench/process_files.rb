require 'find'
require 'timeout'
require 'fileutils'

def process_files(directory)
  results = []

  Find.find(directory) do |path|
    next unless path.end_with?('.p')

    dir = File.dirname(path)
    filename = File.basename(path)

    result = process_file(dir, filename)
    results << result
  end

  results
end

def process_file(dir, filename)
  full_path = File.join(dir, filename)
  output_file = File.join(dir, "#{filename}.log")
  start_time = Time.now
  timeout = 3

  begin
    output = nil
    status = Timeout.timeout(timeout) do
      Dir.chdir(dir) do
        output = `toma #{filename} 2>&1`
      end
    end
    elapsed_time = Time.now - start_time
    File.write(output_file, output)
    result_message = "#{full_path}: Completed in #{elapsed_time.round(2)} seconds"
    File.write(output_file, "#{result_message}\n", mode: 'a')
    result_message
  rescue Timeout::Error
    result_message = "#{full_path}: Timed out"
    File.write(output_file, "#{result_message}\n", mode: 'a')
    result_message
  rescue => e
    result_message = "#{full_path}: Failed with error #{e.message}"
    File.write(output_file, "#{result_message}\n", mode: 'a')
    result_message
  end
end

if ARGV.length != 1
  puts "Usage: ruby script.rb <directory>"
  exit 1
end

directory = ARGV[0]
results = process_files(directory)

results.each do |result|
  puts result
end
