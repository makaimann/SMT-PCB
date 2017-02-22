#!/usr/bin/env python
import setuptools

try:
    reqs = open('requirements.txt', 'r').read().splitlines()
except IOError:
    reqs = []

setuptools.setup(
        name='kicad',
        version='0.1',
        description='KiCad python API',
        author='KiCad Developers',
        author_email='kicad-developers@lists.launchpad.net',
        url='https://github.com/kicad/kicad-python/',
        packages=setuptools.find_packages(exclude=['ez_setup']),
        zip_safe=False,
        install_requires=reqs,
        test_suite='kicad.test.unit')
