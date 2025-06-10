# Copyright 2024 Jiachen Shen.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
# Litex email: <litexlang@outlook.com>
# Litex website: https://litexlang.org
# Litex github repository: https://github.com/litexlang/golitex
# Litex discord server: https://discord.gg/uvrHM7eS

import subprocess
import os

# path = os.path.join(os.path.dirname(__file__), '..', '..', 'examples', 'comprehensive_examples', 'Hilbert_geometry_axioms_formalization.lix')
path = os.path.join(os.path.dirname(__file__), '..', '..', 'examples', 'test_codes', 'tmp.lix')

code = open(path, 'r').read()

subprocess.run(['go', 'run', 'main.go', '-e', code])