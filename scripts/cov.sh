#!/usr/bin/env bash
set -e

docker run -it -d --name cov --mount type=bind,source="$(pwd)"/../kratos,target=/kratos keyiz/garnet-flow bash
docker exec -i cov bash -c "apt update && apt install -y lcov"
docker exec -i cov bash -c "cd /kratos && KRATOS_COVERAGE=1 python3 -m pip install -e ."
docker exec -i cov bash -c "cd /kratos/build/temp.linux-x86_64-3.7 && make -j2"
docker exec -i cov bash -c "cd /kratos/build/temp.linux-x86_64-3.7 && make test"
# do not collect tests
docker exec -i cov bash -c "python3 -m pip install pytest pytest-cov && cd /kratos && pytest --cov-report=xml --cov=kratos tests/"
docker exec -i cov bash -c "cd kratos && lcov --capture --directory . --output-file coverage.info"
# clean up coverage
docker exec -i cov bash -c "cd kratos && lcov --remove coverage.info '/usr/*' --output-file coverage.info"
docker exec -i cov bash -c "cd kratos && lcov --remove coverage.info '*extern*' --output-file coverage.info"
docker exec -i cov bash -c "cd kratos && lcov --list coverage.info"
docker cp cov:/kratos/coverage.info coverage.info
docker cp cov:/kratos/.coverage .coverage

# upload the coverage files
bash <(curl -s https://codecov.io/bash) -f coverage.info
bash <(curl -s https://codecov.io/bash)
