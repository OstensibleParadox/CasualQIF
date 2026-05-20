import os
import re

tsv_path = ".antigravitycli/plans/phase1c-renames.tsv"

with open(tsv_path, 'r') as f:
    lines = f.read().strip().split('\n')[1:] # skip header

renames = []
for line in lines:
    parts = line.split('\t')
    if len(parts) >= 5:
        old_name = parts[0]
        new_name = parts[1]
        kind = parts[2]
        file_path = parts[3]
        count = int(parts[4])
        renames.append((old_name, new_name, kind, file_path, count))

# Sort by length descending to replace longer names first
renames.sort(key=lambda x: len(x[0]), reverse=True)

# Find all lean files
lean_files = []
for root, dirs, files in os.walk("CausalQIF"):
    for file in files:
        if file.endswith(".lean"):
            lean_files.append(os.path.join(root, file))

# 1. Global Replacement
for file_path in lean_files:
    with open(file_path, 'r') as f:
        content = f.read()
    
    orig_content = content
    for old_name, new_name, _, _, _ in renames:
        # Use regex to replace exact word boundary
        pattern = r'\b' + re.escape(old_name) + r'\b'
        content = re.sub(pattern, new_name, content)
        
    if content != orig_content:
        with open(file_path, 'w') as f:
            f.write(content)
            
# 2. Add Deprecation Aliases
aliases_by_file = {}
for old_name, new_name, _, file_path, count in renames:
    if count > 0:
        if file_path not in aliases_by_file:
            aliases_by_file[file_path] = []
        aliases_by_file[file_path].append(f"@[deprecated {new_name}]\nalias {old_name} := {new_name}")

for file_path, aliases in aliases_by_file.items():
    if not os.path.exists(file_path):
        print(f"Warning: file {file_path} does not exist.")
        continue
        
    with open(file_path, 'r') as f:
        content = f.read()
        
    # Find the last `end CausalQIF`
    match = list(re.finditer(r'^end CausalQIF', content, re.MULTILINE))
    if not match:
        print(f"Warning: could not find end CausalQIF in {file_path}")
        continue
        
    last_match = match[-1]
    insert_pos = last_match.start()
    
    # Backtrack if there's a standalone `end` right before it
    before_text = content[:insert_pos]
    end_standalone_match = list(re.finditer(r'^end\s*$', before_text, re.MULTILINE))
    if end_standalone_match:
        # Check if it's the section end
        last_standalone = end_standalone_match[-1]
        # Only backtrack if it's close to the end CausalQIF (e.g. only whitespace between)
        if before_text[last_standalone.end():].strip() == '':
            insert_pos = last_standalone.start()
            
    alias_block = "\n".join(aliases) + "\n\n"
    
    new_content = content[:insert_pos] + alias_block + content[insert_pos:]
    with open(file_path, 'w') as f:
        f.write(new_content)

print("Renames applied successfully.")
