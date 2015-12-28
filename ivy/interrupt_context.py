#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
import signal

class InterruptContext(object):
    def __enter__(self):
        self.interrupted = False
        self.original_handler = signal.getsignal(signal.SIGINT)

        def handler(signum, frame):
            self.interrupted = True

        signal.signal(signal.SIGINT, handler)

        return self

    def __exit__(self, type, value, tb):
        signal.signal(signal.SIGINT, self.original_handler)

if __name__ == '__main__':
    from time import sleep

    i = 0
    with InterruptContext() as c:
        while True:
            i += 1
            print i
            sleep(3)
            print c.interrupted
            c.interrupted = False
            print
