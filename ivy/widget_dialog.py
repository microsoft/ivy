#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This is a custom IPython widget that displays a FlexBox inside a
dialog
"""

from IPython.html import widgets
from IPython.utils.traitlets import Unicode, Bool, Any


class DialogWidget(widgets.FlexBox):
    _view_module = Unicode('nbextensions/ivy/js/widget_dialog', sync=True)
    _view_name = Unicode('DialogView', sync=True)
    options = Any(sync=True, doc="Options to jqueryui dialog and dialogExtend " +
                  "Supports 'max' for height/width properties")
    title = Unicode(sync=True, doc="Overrides options.title, updatable")

    def __init__(self, title, options, **kwargs):
        kwargs['title'] = title
        kwargs['options'] = options
        super(DialogWidget, self).__init__(**kwargs)
