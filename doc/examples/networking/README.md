
To test network components against our specs, we will use a network
emulator called GNS3. GNS3 allows you to creat a simulation of a
network using simulated components such as switches and routers, as
well as virtual hosts. It can also run a real switch operating system
on an emulation of the switch hardware, though we may not get that
far.

Setting up GNS3
===============

To get started, we need to install GNS3 on a Linux machine. Instructions
are here:

    http://docs.gns3.com/1QXVIihk7dsOL7Xr7Bmz4zRzTsJ02wklfImGuHwTlaA4/index.html
    
Make sure to follow all of the instructions, including installing
Docker, which is the virtual environment we will use for our virtual
hosts.

Run through the tutorial to make sure your installation works and that you
understand the basics of setting up a network configuration in GNS3.

    http://docs.gns3.com/1wr2j2jEfX6ihyzpXzC23wQ8ymHzID4K3Hn99-qqshfg/index.html
    
    
Creating a docker container with your tester(s)
===============================================

Copy the Z3 library into this directory:

    cp ~/ivy/ivy/lib/libz3.so .

Compile your Ivy tester(s):

    ivyc udp_test.ivy

Build the container:

    sudo docker build --tag=networking .

List your containers:

    sudo docker container ls

    ... should see networking in the list ...
    
Test the container:

    sudo docker run -i -t --network host networking

    ...container starts...

    # ./udp_test
    
    ...some events are printed...
    test_completed
    
    # exit

(optional) Upload to the repository:

This step only needed if you want to share your container with others.

    sudo docker tag <IMAGE ID> <userid>/networking:v0.X
    sudo docker push <userid>/networking

Here <userid> is your docker repository account name.

Add the container to GNS3 network simulator (see
http://docs.gns3.com/1KGkv1Vm5EgeDusk1qS1svacpuQ1ZUQSVK3XqJ01WKGc/):

Insider GNS3:

1) Use Edit->Pereferences->Docker->Docker Containers
2) Click the New button
3) Select networking:latest
4) Click Next
5) Click Next
6) Click Next (first change the number of network adapters if desired)
7) Click Next
8) Click Next
9) Click Finish
10) Click OK

Now the networking container is available to add to your model.

Add an instance of the container to a GNS3 model:

1) Click the devices button on the left (second from the bottom)
2) Drag the networking device onto the canvas
3) Connect its eth0 port to a switch (bottom button on left)
4) Right-click it and select 'Start'
5) Right-click it and select 'Console'
6) In the terminal window, enter a command to run your tester:

    ./udp_test
    
You should see some events output. 

Testing IP
==========

See the file IP.md for instructions on testing using the IP specification.




