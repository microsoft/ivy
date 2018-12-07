# Packaging instructions

## Linux

### Debian/Ubuntu

- Rename this directory to ms-ivy-X.Y where X.Y is the version number
- Edit the files in debian/ to reflect the current version number
- Run 'make builddeb'
- The .deb file appears in the parent directory

## Windows

The following should work if updates to dependencies (including python
itself) are not needed:

- Install the latest existing release in C:\
- Run these commands:

    > c:\ivy\scripts\activate
    > python setup.py install

- Make an archive of c:/ivy such that the archive has a top-level directory 'ivy'.

