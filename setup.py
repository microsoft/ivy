from setuptools import setup, find_packages

setup(name='ms_ivy',
      version='0.1',
      description='IVy verification tool',
      url='http://github.com/microsoft/ivy',
      author='IVy team',
      author_email='nomail@example.com',
      license='MIT',
      packages=find_packages(),
      package_data={'ivy':['include/*.ivy','include/*.h']},
      install_requires=[
          'ply',
          'tarjan'
      ],
      entry_points = {
        'console_scripts': ['ivy=ivy.ivy:main','ivy_check=ivy.ivy_check:main','ivy_to_cpp=ivy.ivy_to_cpp:main','ivy_show=ivy.ivy_show:main','ivy_ev_viewer=ivy.ivy_ev_viewer:main',],
        },
      zip_safe=False)

