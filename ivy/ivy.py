#! /usr/bin/env python
#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

from ivy_init import ivy_init 
import ivy_module
from tk_ui import ui_main_loop

def main():
    import signal
    signal.signal(signal.SIGINT,signal.SIG_DFL)
    with ivy_module.Module():
        ui_main_loop(ivy_init())

if __name__ == "__main__":
    main()

