#!/bin/sh
set -e

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
    docker cp ~/.pypirc manylinux:/home/
    docker exec -i manylinux bash -c 'cd /kratos && for PYBIN in cp35 cp36 cp37; do /opt/python/${PYBIN}-${PYBIN}m/bin/python setup.py bdist_wheel; done'
    docker exec -i manylinux bash -c 'cd /kratos && for WHEEL in dist/*.whl; do auditwheel repair "${WHEEL}"; done'
    docker exec -i manylinux bash -c 'cd /kratos && twine upload --config-file /home/.pypirc wheelhouse/*'
elif [[ "$TRAVIS_OS_NAME" == "osx" ]]; then
    ls dist/*
else
    ls dist/*
fi
