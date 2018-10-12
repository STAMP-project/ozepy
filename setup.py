#
# OZEPy
#
# Copyright (C) 2017, 2018 SINTEF Digital
# All rights reserved.
#
# This software may be modified and distributed under the terms
# of the MIT license.  See the LICENSE file for details.
#


from setuptools import setup

from ozepy import __VERSION__


setup(name="ozepy",
      version=__VERSION__,
      description="Z3 front-end on object-oriented systems - an Alloy-like modeller, but on an SMT solver!",
      author="Hui Song",
      author_email="hui.song@sintef.no",
      url="https://github.com/STAMP-project/ozepy",
      py_modules=["ozepy"],
      test_suite="tests",
     )
