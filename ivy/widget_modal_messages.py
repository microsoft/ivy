#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
Widget for displaying a modal dialog of messages.

Multiple messages may be grouped into the same dialog.
"""

from IPython.html import widgets
from IPython.utils.traitlets import Unicode

class ModalMessagesWidget(widgets.Widget):
    _view_module = Unicode('nbextensions/ivy/js/widget_modal_messages', sync=True)
    _view_name = Unicode('ModalMessagesView', sync=True)

    def new_message(self, title, body):
        """
        Send a new message, title and body are strings
        """
        self.send({
            "method": "new_message",
            "title": title,
            "body": body,
        })
