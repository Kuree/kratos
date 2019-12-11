import pytest
import kratos


@pytest.fixture(autouse=True)
def clear_kratos_context():
    kratos.clear_context()
