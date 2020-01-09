#!/usr/bin/env bash
set -e

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
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
fi
