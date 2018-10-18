import codecs
import os

from setuptools import setup, find_packages


# Get the long description from the README file
here = os.path.abspath(os.path.dirname(__file__))
try:
  with codecs.open(os.path.join(here, 'README.md'), encoding='utf-8') as f:
      long_description = f.read()
except:
  # This happens when running tests
  long_description = None

setup(name='ms_ivy',
      version='0.1',
      description='IVy verification tool',
      long_description=long_description,
      url='https://github.com/microsoft/ivy',
      author='IVy team',
      author_email='nomail@example.com',
      license='MIT',
      packages=find_packages(),
      package_data={'ivy':['include/*/*.ivy','include/*/*.h']},
      install_requires=[
          'ply',
          'tarjan'
      ],
      entry_points = {
        'console_scripts': ['ivy=ivy.ivy:main','ivy_check=ivy.ivy_check:main','ivy_to_cpp=ivy.ivy_to_cpp:main','ivy_show=ivy.ivy_show:main','ivy_ev_viewer=ivy.ivy_ev_viewer:main','ivy_to_md=ivy.ivy_to_md:main',],
        },
      zip_safe=False)

