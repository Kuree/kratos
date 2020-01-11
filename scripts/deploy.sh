#!/usr/bin/env bash
set -e

if [[ "$OS" == "linux" ]]; then
    if [[ "$BUILD_WHEEL" == true ]]; then
        docker cp ~/.pypirc manylinux:/home/
        docker exec -i manylinux bash -c 'cd /kratos && for PYBIN in cp36 cp37; do /opt/python/${PYBIN}-${PYBIN}m/bin/python setup.py bdist_wheel; done'
        # python 3.8 has different name now
        docker exec -i manylinux bash -c 'cd /kratos && /opt/python/cp38-cp38/bin/python setup.py bdist_wheel'
        docker exec -i manylinux bash -c 'cd /kratos && for WHEEL in dist/*.whl; do auditwheel repair "${WHEEL}"; done'
        docker exec -i manylinux bash -c 'cd /kratos && twine upload --config-file /home/.pypirc --skip-existing wheelhouse/*'
        # upload the src
        docker exec -i manylinux bash -c 'cd /kratos && python setup.py sdist && twine upload --config-file /home/.pypirc --skip-existing dist/*.gz'
    fi
else if [[ "$OS" == "osx" ]]; then
    for PYTHON_VERSION in 3.6 3.8
    do
        source deactivate
        conda create -q -n env$PYTHON_VERSION python=$PYTHON_VERSION
        source activate env$PYTHON_VERSION
        conda install pip
        python --version

        pip install cmake wheel twine
        CXX=/usr/local/bin/g++-8 python setup.py bdist_wheel
    done

    twine upload --skip-existing dist/*.whl
fi
