# -*- mode: ruby -*-
# vi: set ft=ruby :

require "rbconfig"

# Vagrant configuration (https://docs.vagrantup.com)

Vagrant.configure("2") do |config|

   # the virtualbox provider will always work, so it's the default.
   config.vm.provider "virtualbox" do |vb, override|
      #vb.gui = true
      vb.memory = "2048"
      override.vm.box = "debian/contrib-jessie64"
   end

   # the docker provider is preferable to the virtualbox provider,
   # but seems to only work properly on linux.
   config.vm.provider "docker" do |d, override|
      override.vm.box = "tknerr/baseimage-ubuntu-16.04"
   end

    config.vm.network "forwarded_port", guest: 8888, host: 8888, auto_correct: true

   config.vm.provision "shell", inline: <<-SHELL
      /bin/sh /vagrant/scripts/setup/vagrant.sh
   SHELL

end
