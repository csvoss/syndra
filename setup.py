"""A setuptools based setup module.
See:
https://packaging.python.org/en/latest/distributing.html
https://github.com/pypa/sampleproject
"""

from setuptools import setup, find_packages
from codecs import open
from os import path

here = path.abspath(path.dirname(__file__))


long_description = """
Syndra is an inference engine for rule-based biological models.

It supports making inferences over sets of modeling rules, which allows redundancies to be detected and eliminated from those rules. For example, if we have the rules MEK phosphorylates MAPK and MAPK, when phosphorylated, is active, Syndra can confirm that these rules imply MEK activates MAPK.

Syndra can also detect when a set of rules are mutually incompatible. For example, Syndra can detect that no model is compatible with the two rules A, when phosphorylated, is active and A, when phosphorylated, is inactive both at once.

Finally, it supports inferring gaps in sets of model rules. Given a set of facts which, when combined, are enough to deduce a single model, but which might not necessarily be rules themselves, Syndra can deduce the satisfying model.

This system works by translating each rule into predicates in the iota language, a logic designed by Adrien Husson and Jean Krivine to describe predicates over rule-based biological models. Our inferences about these predicates are then powered by the z3 theorem prover.
"""


setup(
    name='syndra',
    version='1.0',
    description='Logical deduction tool for analyzing high-level queries about the chemical representations of biological models',
    long_description=long_description,
    url='https://github.com/csvoss/syndra',
    author='Chelsea Voss',
    author_email='csvoss@mit.edu',
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
    packages=['engine'],
    install_requires=['nose'],
    test_suite='nose.collector',
    tests_require=['nose'],
    zip_safe=False
)
