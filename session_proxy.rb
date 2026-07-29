target = "scripts/textbooks_drafts/Number-Theory-For-Beginners/section13.lit"
target_name = "thm gaussian_prime_norm_is_rational_prime:"
child = IO.popen(["target/release/litex", "-compact", "-session", "-before", target], "r+")
child.sync = true

ready = child.gets
abort("session did not become ready") unless ready&.include?('"event":"ready"')

lines = File.readlines(target)
starts = []
lines.each_with_index do |line, index|
  starts << index if line.match?(/\A(?:have|thm|prop|claim|abstract_prop|struct|template|know|import)\b/)
end
target_index = starts.find_index { |index| lines[index].start_with?(target_name) }
abort("target theorem not found") unless target_index

starts.first(target_index).each_with_index do |start_index, replay_index|
  end_index = starts[replay_index + 1] || lines.length
  source = "try:\n" + lines[start_index...end_index].map { |line| "    #{line}" }.join
  child.write("run replay_#{replay_index + 1} #{source.bytesize}\n")
  child.write(source)
  child.flush
  event = child.gets
  abort("replay #{replay_index + 1} produced no event") unless event
  abort(event) unless event.include?('"ok":true')
  puts %({"event":"replay_ok","index":#{replay_index + 1},"line":#{start_index + 1}})
  STDOUT.flush
end

puts %({"event":"proxy_ready","replayed":#{target_index},"mode":"project"})
STDOUT.flush

while (header = STDIN.gets)
  if header == "close\n"
    child.write(header)
    child.flush
    puts(child.gets || %({"event":"closed"}))
    break
  end

  match = header.match(/\Afile\s+(\S+)\s+(.+)\n\z/)
  abort("invalid proxy header") unless match
  source = File.read(match[2])
  child.write("run #{match[1]} #{source.bytesize}\n")
  child.write(source)
  child.flush
  event = child.gets
  abort("candidate produced no event") unless event
  puts event
  STDOUT.flush
end
