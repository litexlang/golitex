require "json"
require "open3"

file = ARGV.fetch(0)
stop_name = ARGV.fetch(1)
source = File.read(file)
starts = []
source.each_line.with_index do |line, index|
  if line.match?(/\A(?:have fn|have|prop|thm|axiom|claim|template)[ \t]/)
    starts << index
  end
end
lines = source.lines
blocks = starts.each_with_index.map do |start, index|
  finish = index + 1 < starts.length ? starts[index + 1] : lines.length
  lines[start...finish].join.rstrip
end
stop_index = blocks.index { |block| block.match?(/\A(?:prop|thm|have fn|have) #{Regexp.escape(stop_name)}(?:\W|\z)/) }
abort("stop declaration not found: #{stop_name}") unless stop_index

def wrapped(block)
  payload = "try:\n" + block.each_line.map { |line| "    #{line}" }.join
  payload.end_with?("\n") ? payload : "#{payload}\n"
end

def submit(stdin, stdout, id, block)
  payload = wrapped(block)
  stdin.write("run #{id} #{payload.bytesize}\n")
  stdin.write(payload)
  stdin.flush
  line = stdout.gets
  abort("session ended while waiting for #{id}") unless line
  event = JSON.parse(line)
  puts("#{id}: #{event["ok"] ? "ok" : "FAILED"}")
  puts(event["trace"]) unless event["ok"]
  event
end

cmd = [
  "target/release/litex",
  "-compact",
  "-session",
  "-before",
  file,
]

Open3.popen3(*cmd) do |stdin, stdout, stderr, wait_thread|
  ready = stdout.gets
  abort("session produced no ready event: #{stderr.read}") unless ready
  puts(ready)

  blocks[0...stop_index].each_with_index do |block, index|
    event = submit(stdin, stdout, "replay-#{index + 1}", block)
    abort("replay failed at block #{index + 1}") unless event["ok"]
  end

  puts("READY_FOR_CANDIDATES")
  STDIN.each_line.with_index do |path, index|
    path = path.strip
    next if path.empty?
    break if path == "close"
    event = submit(stdin, stdout, "candidate-#{index + 1}", File.read(path))
    puts(JSON.generate(event))
  end

  stdin.write("close\n")
  stdin.flush
  wait_thread.join
end
