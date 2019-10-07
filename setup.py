import os
import re
import sys
import platform
import subprocess
import shutil

from setuptools import setup, Extension
from setuptools.command.build_ext import build_ext
from distutils.version import LooseVersion


class CMakeExtension(Extension):
    def __init__(self, name, sourcedir=''):
        Extension.__init__(self, name, sources=[])
        self.sourcedir = os.path.abspath(sourcedir)


class CMakeBuild(build_ext):
    def run(self):
        try:
            out = subprocess.check_output(['cmake', '--version'])
        except OSError:
            raise RuntimeError(
                "CMake must be installed to build the following extensions: " +
                ", ".join(e.name for e in self.extensions))

        if platform.system() == "Windows":
            cmake_version = LooseVersion(
                re.search(r'version\s*([\d.]+)', out.decode()).group(1))
            if cmake_version < '3.1.0':
                raise RuntimeError("CMake >= 3.1.0 is required on Windows")

        for ext in self.extensions:
            self.build_extension(ext)

    def build_extension(self, ext):
        extdir = os.path.abspath(
            os.path.dirname(self.get_ext_fullpath(ext.name)))
        cmake_args = ['-DCMAKE_LIBRARY_OUTPUT_DIRECTORY=' + extdir,
                      '-DPYTHON_EXECUTABLE=' + sys.executable]

        cfg = 'Debug' if self.debug else 'Release'
        build_args = ['--config', cfg]

        if platform.system() == "Windows":
            cmake_args += [
                '-DCMAKE_LIBRARY_OUTPUT_DIRECTORY_{}={}'.format(cfg.upper(),
                                                                extdir)]
            cmake_args += ["-G", "MinGW Makefiles"]
        else:
            cmake_args += ['-DCMAKE_BUILD_TYPE=' + cfg]
            build_args += ['--', '-j2']

        python_path = sys.executable
        cmake_args += ['-DPYTHON_EXECUTABLE:FILEPATH=' + python_path]

        env = os.environ.copy()
        env['CXXFLAGS'] = '{} -DVERSION_INFO=\\"{}\\"'.format(
            env.get('CXXFLAGS', ''),
            self.distribution.get_version())
        if not os.path.exists(self.build_temp):
            os.makedirs(self.build_temp)
        subprocess.check_call(['cmake', ext.sourcedir] + cmake_args,
                              cwd=self.build_temp, env=env)
        subprocess.check_call(
            ['cmake', '--build', '.', "--target", "_kratos"] + build_args,
            cwd=self.build_temp)


current_directory = os.path.abspath(os.path.dirname(__file__))
with open(os.path.join(current_directory, 'README.rst')) as f:
    long_description = f.read()

setup(
    name='kratos',
    packages=[
        "kratos"
    ],
    version='0.0.16',
    author='Keyi Zhang',
    author_email='keyi@stanford.edu',
    description='Kratos is a fast hardware design language embedded in Python',
    url="https://github.com/Kuree/kratos",
    ext_modules=[CMakeExtension('_kratos')],
    cmdclass=dict(build_ext=CMakeBuild),
    zip_safe=False,
    python_requires=">=3.5",
    install_requires=[
        "astor",
    ],
    long_description=long_description,
    long_description_content_type='text/x-rst',
)
