import pytest
import kratos


@pytest.fixture(autouse=True)
def clear_kratos_context():
    kratos.Generator.clear_context()

