#!/usr/bin/env bash
set -e

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
    docker pull keyiz/manylinux
    docker pull keyiz/garnet-flow
    docker run -d --name manylinux --rm -it --mount type=bind,source="$(pwd)"/../kratos,target=/kratos keyiz/manylinux bash
    docker run -d --name manylinux-test --rm -it --mount type=bind,source="$(pwd)"/../kratos,target=/kratos  keyiz/garnet-flow bash

    docker cp ../kratos manylinux:/
    docker exec -i manylinux bash -c "pip install conan"
    docker exec -i manylinux bash -c 'cd kratos && python setup.py bdist_wheel'
    docker exec -i manylinux bash -c 'cd kratos && auditwheel show dist/*'
    docker exec -i manylinux bash -c 'cd kratos && auditwheel repair dist/*'
    docker exec -i manylinux-test bash -c 'cd kratos && pip install pytest dist/* && pytest -v tests/'

elif [[ "$TRAVIS_OS_NAME" == "osx" ]]; then
    export PYTHON=3.7.0
    brew install gcc
    brew install pyenv-virtualenv
    pyenv install ${PYTHON}
    export PYENV_VERSION=$PYTHON
    export PATH="/Users/travis/.pyenv/shims:${PATH}"
    pyenv virtualenv venv37
    source /Users/travis/.pyenv/versions/${PYTHON}/envs/venv37/bin/activate
    python --version

    python -m pip install cmake twine wheel pytest conan
    export CXX=`which g++`
    echo $CXX
    python setup.py bdist_wheel
    pip install dist/*.whl
    pytest tests/
else
    python --version
    pip install conan wheel pytest
    export CXX=`which g++`
    echo $CXX
    python setup.py bdist_wheel
    pip install dist/*.whl
    pytest tests/
fi

echo [distutils]                                  > ~/.pypirc
echo index-servers =                             >> ~/.pypirc
echo "  pypi"                                    >> ~/.pypirc
echo                                             >> ~/.pypirc
echo [pypi]                                      >> ~/.pypirc
echo repository=https://upload.pypi.org/legacy/  >> ~/.pypirc
echo username=keyi                               >> ~/.pypirc
echo password=$PYPI_PASSWORD                     >> ~/.pypirc
