import codecs
import os
import platform

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
      version='0.3',
      description='IVy verification tool',
      long_description=long_description,
      url='https://github.com/microsoft/ivy',
      author='IVy team',
      author_email='nomail@example.com',
      license='MIT',
      packages=find_packages(),
      package_data=({'ivy':['include/*/*.ivy','include/*/*.h','include/*.h','lib/*.dll','lib/*.lib','z3/*.dll']}
                    if platform.system() == 'Windows' else
                    {'ivy':['include/*/*.ivy','include/*/*.h','include/*.h','lib/*.dylib','lib/*.a','z3/*.dylib']}
                    if platform.system() == 'Darwin' else
                    {'ivy':['include/*/*.ivy','include/*/*.h','include/*.h','lib/*.so','lib/*.a','z3/*.so','ivy2/s3/ivyc_s3']}),
      install_requires=[
          'ply',
          'tarjan'
      ],
      entry_points = {
        'console_scripts': ['ivy=ivy.ivy:main','ivy_check=ivy.ivy_check:main','ivy_to_cpp=ivy.ivy_to_cpp:main','ivy_show=ivy.ivy_show:main','ivy_ev_viewer=ivy.ivy_ev_viewer:main','ivyc=ivy.ivy_to_cpp:ivyc','ivy_to_md=ivy.ivy_to_md:main','ivy_libs=ivy.ivy_libs:main'],
        },
      zip_safe=False)

