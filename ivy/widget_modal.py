#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This is a custom IPython widget that displays a FlexBox inside a
Boostrap modal with OK and Cancel buttons
"""

from IPython.html import widgets
from IPython.html.widgets.widget import CallbackDispatcher
from IPython.utils.traitlets import Unicode, Bool, Any


class ModalWidget(widgets.FlexBox):
    _view_module = Unicode('nbextensions/ivy/js/widget_modal', sync=True)
    _view_name = Unicode('ModalView', sync=True)
    title = Unicode('', sync=True)

    def __init__(self, title, **kwargs):
        kwargs['title'] = title
        super(ModalWidget, self).__init__(**kwargs)
        self._close_handlers = CallbackDispatcher()
        self.on_msg(self._handle_modal_msg)

    def on_close(self, callback, remove=False):
        """
        Register a callback to execute when the modal is closed.

        The callback will be called with two arguments, the
        ModalWidget object and the name of the close button clicked.

        Parameters
        ----------
        remove : bool (optional)
            Set to true to remove the callback from the list of callbacks.
        """
        self._close_handlers.register_callback(callback, remove=remove)

    def _handle_modal_msg(self, _, content):
        if content['event'] == 'button':
            self._close_handlers(self, content['button'])
        else:
            assert False, content
