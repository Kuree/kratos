import subprocess
import os
import pytest
import tempfile


# get all example code
root_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
example_dir = os.path.join(root_dir, "examples")
files = os.listdir(example_dir)
filenames = []
for fn in files:
    fn_ = os.path.join(example_dir, fn)
    if os.path.isfile(fn_) and os.path.splitext(fn_)[-1] == ".py":
        # we only put the basename of filename here so that in the pytest
        # verbose printout, we won't have user's dir info
        filenames.append(fn)


@pytest.mark.parametrize("filename", filenames)
def test_examples(filename):
    filename = os.path.join(example_dir, filename)
    # use a temp dir
    with tempfile.TemporaryDirectory() as temp:
        args = ["python", filename]
        subprocess.check_call(args, cwd=temp)
