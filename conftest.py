import pytest
import kratos
import os
import tempfile
import filecmp


def get_gold_dir():
    return os.path.join(os.path.dirname(__file__), "tests", "gold")


def check_gold_fn(mod, gold_name, **kargs):
    with tempfile.TemporaryDirectory() as tempdir:
        filename = os.path.join(tempdir, "test.sv")
        gold = os.path.join(get_gold_dir(), gold_name + ".sv")
        if isinstance(mod, kratos.Generator):
            kratos.verilog(mod, filename=filename, **kargs)
        else:
            with open(filename, "w+") as f:
                f.write(mod)
        assert os.path.isfile(gold)
        assert os.path.isfile(filename)
        if not filecmp.cmp(filename, gold):
            with open(filename) as f:
                print(f.read())
            print("-" * 80)
            with open(gold) as f:
                print(f.read())
            assert False


def check_file_fn(src_str, gold_filename):
    gold = os.path.join(get_gold_dir(), gold_filename)
    with open(gold) as f:
        gold_text = f.read()
        if os.path.isfile(src_str):
            with open(src_str) as ff:
                src_str = ff.read()
        if src_str != gold_text:
            print(src_str)
            print("-" * 80)
            print(gold_text)
            assert False


@pytest.fixture(autouse=True)
def clear_kratos_context():
    kratos.clear_context()


@pytest.fixture
def check_gold():
    return check_gold_fn


@pytest.fixture
def check_file():
    return check_file_fn
