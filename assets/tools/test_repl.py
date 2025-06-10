import subprocess
import os

# path = os.path.join(os.path.dirname(__file__), '..', '..', 'examples', 'comprehensive_examples', 'Hilbert_geometry_axioms_formalization.lix')
path = os.path.join(os.path.dirname(__file__), '..', '..', 'examples', 'test_codes', 'tmp.lix')

code = open(path, 'r').read()

subprocess.run(['go', 'run', 'main.go', '-e', code])