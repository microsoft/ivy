# Packaging instructions

Ivy is packaged as a python "wheel". 

## Building and uploading a wheel

1. Install Ivy as usual (see `doc/install.md`)

2. Set the version nummber in `setup.py`

3. Build a wheel like this:

        $ python setup.py bdist_wheel --plat-name <platform-name>
        
    where `<platform-name>` is:
    
    - for linux: `manylinux1_x86_64`
    - for Windows: `win_amd64`
    - for MacOS 10.9: `macosx_10_9_x86_64`
    
    The distribution is created as a `.whl` file in directory `dist`. 

4. Upload a wheel like this:

        $ pip install twine
        $ twine upload dist/*
        
## Debian/Ubuntu

It is also possible to build a debian package, though this is
obsolete. 

1. Rename this directory to ms-ivy-X.Y where X.Y is the version number
2. Edit the files in debian/ to reflect the current version number
3. Run 'make builddeb'
4. The .deb file appears in the parent directory

