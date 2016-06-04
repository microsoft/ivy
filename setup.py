from setuptools import setup

setup(name='ms_ivy',
      version='0.1',
      description='IVy verification tool',
      url='http://github.com/microsoft/ivy',
      author='IVy team',
      author_email='nomail@example.com',
      license='MIT',
      packages=['ivy'],
      install_requires=[
          'ply',
          'pygraphviz',
          'tarjan'
      ],
      entry_points = {
        'console_scripts': ['ivy=ivy.ivy:main','ivy_check=ivy.ivy_check:main','ivy_to_cpp=ivy.ivy_to_cpp:main',],
        },
      zip_safe=False)

