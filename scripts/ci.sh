#!/usr/bin/env bash
set -xe

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
    if [[ "$BUILD_WHEEL" == true ]]; then
        docker pull keyiz/manylinux
        docker pull keyiz/garnet-flow
        docker run -d --name manylinux --rm -it --mount type=bind,source="$(pwd)"/../kratos,target=/kratos keyiz/manylinux bash
        docker run -d --name manylinux-test --rm -it --mount type=bind,source="$(pwd)"/../kratos,target=/kratos  keyiz/garnet-flow bash

        docker exec -i manylinux bash -c 'cd kratos && python setup.py bdist_wheel'
        docker exec -i manylinux bash -c 'cd kratos && auditwheel show dist/*'
        docker exec -i manylinux bash -c 'cd kratos && auditwheel repair dist/*'
        docker exec -i manylinux-test bash -c 'cd kratos && pip install pytest dist/* && pytest -v tests/'
    else
        docker pull keyiz/garnet-flow
        docker run -d --name manylinux-test --rm -it --mount type=bind,source="$(pwd)"/../kratos,target=/kratos  keyiz/garnet-flow bash

        docker exec -i manylinux-test bash -c 'cd kratos && mkdir build && cd build && cmake ..'
        docker exec -i manylinux-test bash -c "cd kratos/build && make -j2"
        docker exec -i manylinux-test bash -c "cd kratos/build && make test"
    fi

elif [[ "$TRAVIS_OS_NAME" == "osx" ]]; then
    wget https://repo.anaconda.com/miniconda/Miniconda3-latest-MacOSX-x86_64.sh -O miniconda.sh
    chmod +x miniconda.sh
    ./miniconda.sh -b -p $TRAVIS_BUILD_DIR/miniconda
    export PATH=$TRAVIS_BUILD_DIR/miniconda/bin:$PATH
    hash -r
    conda config --set always_yes yes --set changeps1 no
    conda update -q conda
    conda create -q -n env python=3.7.0
    source activate env
    python --version
    conda install pip

    pip install cmake twine wheel pytest
    python setup.py bdist_wheel
    pip install dist/*.whl
    pytest tests/
else
    python --version
    pip install wheel pytest twine
    python setup.py bdist_wheel
    pip install dist/*.whl
fi

echo [distutils]                                  > ~/.pypirc
echo index-servers =                             >> ~/.pypirc
echo "  pypi"                                    >> ~/.pypirc
echo                                             >> ~/.pypirc
echo [pypi]                                      >> ~/.pypirc
echo repository=https://upload.pypi.org/legacy/  >> ~/.pypirc
echo username=keyi                               >> ~/.pypirc
echo password=$PYPI_PASSWORD                     >> ~/.pypirc

if [[ "$TRAVIS_OS_NAME" == "osx" ]]; then
    set -x
    if [ -n "$TRAVIS_TAG" ]; then
        twine upload dist/*.whl
    fi
fi
