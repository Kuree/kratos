#!/usr/bin/env bash
set -e

if [[ "$OS" == "linux" ]]; then
    if [[ "$BUILD_WHEEL" == true ]]; then
        docker cp ~/.pypirc manylinux:/home/
        docker exec -i manylinux bash -c 'cd /kratos && for PYBIN in cp36 cp37; do /opt/python/${PYBIN}-${PYBIN}m/bin/python setup.py bdist_wheel; done'
        # python 3.8+ has different names now
        docker exec -i manylinux bash -c 'cd /kratos && for PYBIN in cp38 cp39 cp310; do /opt/python/${PYBIN}-${PYBIN}/bin/python setup.py bdist_wheel; done'
        docker exec -i manylinux bash -c 'cd /kratos && for WHEEL in dist/*.whl; do auditwheel repair --plat manylinux2010_x86_64 "${WHEEL}"; done'
        docker exec -i manylinux bash -c 'cd /kratos && twine upload --config-file /home/.pypirc --skip-existing wheelhouse/*'
        # upload the src
        docker exec -i manylinux bash -c 'cd /kratos && python setup.py sdist && twine upload --config-file /home/.pypirc --skip-existing dist/*.gz'
    fi
elif [[ "$OS" == "osx" ]]; then
    export PATH=$HOME/miniconda/bin:$PATH
    for PYTHON_VERSION in 3.6 3.8 3.9 3.10
    do
        conda create -q -n env$PYTHON_VERSION python=$PYTHON_VERSION
        source activate env$PYTHON_VERSION
        conda install pip
        python --version

        pip install cmake wheel twine
        CXX=/usr/local/bin/g++-8 python setup.py bdist_wheel
        conda deactivate
    done
    source activate env3.6
    twine upload --skip-existing dist/*.whl
fi
