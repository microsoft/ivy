# -*- mode: ruby -*-
# vi: set ft=ruby :

# Vagrant configuration (https://docs.vagrantup.com)

Vagrant.configure("2") do |config|

   # the virtualbox provider will always work, so it's the default.
   config.vm.provider "virtualbox" do |vb, override|
      #vb.gui = true
      vb.memory = "2048"
      override.vm.box = "debian/contrib-jessie64"
      # the `vagrant-vbguest` plugin can fail when the guest tools installation
      # prompts for confirmation, so we need to ensure it's not interactive.
      if Vagrant.has_plugin? "vagrant-vbguest" then
         config.vbguest.installer_arguments = "--nox11 -- --force"
      end
   end

   # WARNING: vagrant's hyper-v support appears to work infrequently. virtualbox
   # integration is more reliable (ymmv).
   config.vm.provider "hyperv" do |hyperv, override|
      #hyperv.gui = true
      hyperv.memory = "2048"
      # `hashicorp/precise64` hit a roadblock when trying to compile ocaml, so
      # an alternative box with a newer distro needed to be used.
      override.vm.box = "nikel/xerus64"
   end

   # docker appears to be an unpopular vagrant provider (the most popular box
   # has only 184 downloads at the moment this sentence is being written!). i
   # prefer the docker provider to more heavyweight virtualization providers,
   # however, but the docker provider seems to only work properly on linux.
   config.vm.provider "docker" do |d, override|
      # NOTE: you may need to manually pull this box before issuing a
      #`vagrant up --provider=docker` on older versions of vagrant.
      override.vm.box = "tknerr/baseimage-ubuntu-16.04"
   end

   config.ssh.forward_x11 = true

   config.vm.provision "shell", inline: <<-SHELL
      /bin/sh /vagrant/scripts/setup/vagrant.sh
   SHELL

end
