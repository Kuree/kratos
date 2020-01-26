#!/usr/bin/env bash
set -e

if [[ "$OS" == "linux" ]]; then
    if [[ "$BUILD_WHEEL" == true ]]; then
        docker pull keyiz/manylinux
        docker pull keyiz/kratos:test
        docker run -d --name manylinux --rm -it --mount type=bind,source="$(pwd)"/../kratos,target=/kratos keyiz/manylinux bash
        docker run -d --name manylinux-test --rm -it --mount type=bind,source="$(pwd)"/../kratos,target=/kratos  keyiz/kratos:test bash

        docker exec -i manylinux bash -c 'cd kratos && python setup.py bdist_wheel'
        docker exec -i manylinux bash -c 'cd kratos && auditwheel show dist/*'
        docker exec -i manylinux bash -c 'cd kratos && auditwheel repair dist/*'
        docker exec -i manylinux-test bash -c 'cd kratos && pip install pytest wheelhouse/* && pytest -v tests/'
    elif [[ "$BUILD_WHEEL" == false ]]; then
        docker pull keyiz/kratos:test
        docker run -d --name manylinux-test --rm -it --mount type=bind,source="$(pwd)"/../kratos,target=/kratos  keyiz/kratos:test bash

        docker exec -i manylinux-test bash -c 'cd kratos && mkdir build && cd build && cmake .. -DCMAKE_BUILD_TYPE=Debug'
        docker exec -i manylinux-test bash -c "cd kratos/build && make -j2"
        docker exec -i manylinux-test bash -c "cd kratos/build && ctest -T memcheck"
    else
        docker pull keyiz/clang-tidy
        docker run -d --name manylinux-test --rm -it --mount type=bind,source="$(pwd)"/../kratos,target=/kratos  keyiz/clang-tidy bash

        docker exec -i manylinux-test bash -c 'cd kratos && mkdir build && cd build && cmake -DUSE_CLANG_TIDY=TRUE ..'
        docker exec -i manylinux-test bash -c "cd kratos/build && make kratos -j2"
    fi

elif [[ "$OS" == "osx" ]]; then
    wget --quiet https://repo.anaconda.com/miniconda/Miniconda3-latest-MacOSX-x86_64.sh -O miniconda.sh
    chmod +x miniconda.sh
    ./miniconda.sh -b -p $HOME/miniconda
    export PATH=$HOME/miniconda/bin:$PATH
    conda config --set always_yes yes --set changeps1 no
    conda create -q -n env3.7 python=3.7
    source activate env3.7
    conda install pip
    python --version

    python -m pip install scikit-build
    python -m pip install cmake twine wheel pytest
    CXX=/usr/local/bin/g++-8 python setup.py bdist_wheel
    pip install dist/*.whl
    pytest -v tests/
else
    python --version
    python -m pip install wheel pytest twine
    python setup.py bdist_wheel
    python -m pip install --find-links=dist kratos
    python -m pytest -v tests/
fi

echo [distutils]                                  > ~/.pypirc
echo index-servers =                             >> ~/.pypirc
echo "  pypi"                                    >> ~/.pypirc
echo                                             >> ~/.pypirc
echo [pypi]                                      >> ~/.pypirc
echo repository=https://upload.pypi.org/legacy/  >> ~/.pypirc
echo username=keyi                               >> ~/.pypirc
echo password=$PYPI_PASSWORD                     >> ~/.pypirc

