from setuptools import setup, find_packages
from os import path

here = path.abspath(path.dirname(__file__))
with open(here + "/README.md", "r") as fh:
    long_description = fh.read()
with open(here + "/requirements.txt", "r") as f:
    install_requires = f.read().splitlines()

setup(
    name="ontodev-nanobot",
    version="0.0.1",
    description="",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/ontodev/nanobot",
    author="Rebecca C Jackson",
    author_email="rbca.jackson@gmail.com",
    classifiers=[  # Optional
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Developers",
        "Programming Language :: Python :: 3.6",
        "Programming Language :: Python :: 3.7",
        "Programming Language :: Python :: 3.8",
    ],
    install_requires=install_requires,
    packages=find_packages(exclude="test"),
    python_requires=">=3.6, <4",
    package_data={"nanobot": ["templates/*.html"]},
)
