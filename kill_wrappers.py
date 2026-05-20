import os
import re

kills = [
    ("pmfMargOutFst", "marginalizeOutFst"),
    ("equivMargOutFst", "equivMarginalizeOutFst"),
    ("pmfMargOutSnd", "marginalizeOutSnd"),
    ("equivMargOutSnd", "equivMarginalizeOutSnd"),
]

# 1. Global Replacement in all files EXCEPT Reshapes.lean
lean_files = []
for root, dirs, files in os.walk("CausalQIF"):
    for file in files:
        if file.endswith(".lean"):
            lean_files.append(os.path.join(root, file))

for file_path in lean_files:
    if "Reshapes.lean" in file_path: continue
    with open(file_path, 'r') as f:
        content = f.read()
    
    orig_content = content
    for old_name, new_name in kills:
        pattern = r'\b' + re.escape(old_name) + r'\b'
        content = re.sub(pattern, new_name, content)
        
    if content != orig_content:
        with open(file_path, 'w') as f:
            f.write(content)

# 2. Modify Reshapes.lean
reshapes_path = "CausalQIF/Probability/Entropy/ChainRule/Reshapes.lean"
with open(reshapes_path, 'r') as f:
    content = f.read()

# Add import
if "import CausalQIF.Probability.FinitePMF.Marginalize" not in content:
    content = content.replace("import CausalQIF.Probability.Entropy.Basic", 
                              "import CausalQIF.Probability.Entropy.Basic\nimport CausalQIF.Probability.FinitePMF.Marginalize")

# Remove equivMargOutSnd
equiv_snd_pat = r"def equivMargOutSnd.*?(?=def pmfMargOutSnd)"
content = re.sub(equiv_snd_pat, "@[deprecated equivMarginalizeOutSnd]\nalias equivMargOutSnd := equivMarginalizeOutSnd\n\n", content, flags=re.DOTALL)

# Remove pmfMargOutSnd
pmf_snd_pat = r"def pmfMargOutSnd.*?(?=def equivMargOutFst)"
content = re.sub(pmf_snd_pat, "@[deprecated marginalizeOutSnd]\nalias pmfMargOutSnd := marginalizeOutSnd\n\n", content, flags=re.DOTALL)

# Remove equivMargOutFst
equiv_fst_pat = r"def equivMargOutFst.*?(?=def pmfMargOutFst)"
content = re.sub(equiv_fst_pat, "@[deprecated equivMarginalizeOutFst]\nalias equivMargOutFst := equivMarginalizeOutFst\n\n", content, flags=re.DOTALL)

# Remove pmfMargOutFst
pmf_fst_pat = r"def pmfMargOutFst.*?(?=def equivPairFstSnd)"
content = re.sub(pmf_fst_pat, "@[deprecated marginalizeOutFst]\nalias pmfMargOutFst := marginalizeOutFst\n\n", content, flags=re.DOTALL)

with open(reshapes_path, 'w') as f:
    f.write(content)

print("Kills applied successfully.")
