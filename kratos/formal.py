from _kratos.formal import remove_async_reset as _remove_async_reset
from .passes import verilog
import tempfile
import os
import shutil
import subprocess


def output_btor(generator, filename, remove_async_reset=True, yosys_path="",
                quite=False, **kargs):
    # check yosys
    if yosys_path == "" or not os.path.isfile(yosys_path):
        # need to figure out yosys by ourselves
        yosys_path = shutil.which("yosys")
        assert yosys_path, "Yosys not found"
    # remove async reset if necessary
    if remove_async_reset:
        _remove_async_reset(generator.internal_generator)
    # abs path
    filename = os.path.abspath(filename)

    # I think most of the kratos semantics are supported by yosys
    # if not, you can also turn on the flag to use sv2v to convert
    with tempfile.TemporaryDirectory() as temp:
        verilog_filename = os.path.join(temp, "verilog.sv")
        verilog(generator, filename=verilog_filename, **kargs)
        # need to output the yosys file
        yosys_file = os.path.join(temp, "convert.ys")
        with open(yosys_file, "w+") as f:
            f.write("read_verilog -formal -sv {0}\n".format(verilog_filename))
            f.write("prep -top {0}\n".format(generator.name))
            f.write("flatten\n")
            f.write("write_btor {0}\n".format(filename))

        # call yosys
        extra_args = ["-s"]
        if quite:
            extra_args = ["-q"] + extra_args
        subprocess.check_call([yosys_path] + extra_args + [yosys_file])
