#!/usr/bin/env bash
set -e

docker run -it -d --name cov --mount type=bind,source="$(pwd)"/../kratos,target=/kratos keyiz/kratos:test bash
docker exec -i cov bash -c "cd /kratos && KRATOS_COVERAGE=1 python3 -m pip install -e ."
docker exec -i cov bash -c "cd /kratos/build/temp.linux-x86_64-3.7 && make -j2"
docker exec -i cov bash -c "cd /kratos/build/temp.linux-x86_64-3.7 && make test"
# do not collect tests
docker exec -i cov bash -c "python3 -m pip install pytest pytest-cov && cd /kratos && pytest --cov-report=xml --cov=kratos tests/"
docker exec -i cov bash -c "cd kratos && lcov --capture --directory . --output-file coverage.info"
# clean up coverage
docker exec -i cov bash -c "cd kratos && lcov --remove coverage.info '/usr/*' '*extern*' '*tests*' --output-file coverage.info"
docker exec -i cov bash -c "cd kratos && lcov --list coverage.info"

# upload the coverage files
bash <(curl -s https://codecov.io/bash)
