"""A setuptools based setup module.
See:
https://packaging.python.org/en/latest/distributing.html
https://github.com/pypa/sampleproject
"""

from setuptools import setup, find_packages
from codecs import open
from os import path

here = path.abspath(path.dirname(__file__))


with open(path.join(here, 'README.md'), encoding='utf-8') as f:
    long_description = f.read()

setup(
    name='syndra',
    version='1.0',
    description='Logical deduction tool for analyzing high-level queries about the chemical representations of biological models',
    long_description=long_description,
    url='https://github.com/csvoss/syndra',
    author='Chelsea Voss ',
    license='MIT',
    classifiers=[
        'Development Status :: 3 - Alpha',
        'Intended Audience :: Science/Research',
        'Topic :: Scientific/Engineering :: Medical Science Apps.',
        'Topic :: Scientific/Engineering :: Bio-Informatics',
        'License :: OSI Approved :: MIT License',
        'Programming Language :: Python :: 2',
        'Programming Language :: Python :: 2.6',
        'Programming Language :: Python :: 2.7',
    ],
    keywords='biology z3 Kappa INDRA',
    packages=find_packages(exclude=['contrib', 'docs', 'tests']),
    install_requires=['nose'],
)
