/*
  Copyright (c) Microsoft Corporation. All Rights Reserved.
*/
/*
  This file contains an IPython widget based on
  https://github.com/ROMB/jquery-dialogextend that displays a FlexBox
  in a dialog window.
*/

(function () {
    "use strict";

    var ivy_lib_path = "/nbextensions/ivy/lib/";

    require.config({
        paths: {
            "jquery-dialogextend": ivy_lib_path + "jquery-dialogextend-2.0.4/jquery.dialogextend",
        },

        shim: {
            "jqueryui-dialogextend": {
                deps: ["jquery", "jqueryui"],
            },
        },
    });

})();


define([
    "widgets/js/widget_box",
    "jquery",
    "jqueryui",
    "jquery-dialogextend",
], function (widget_box, $) {
    "use strict";

    window._dialog_widget_views = [];

    /*
      Override some dialog methods to get rid of strange behaviors /
      bugs. Most severely, reloading of iframes when switching
      dialogs.
    */

    // _moveToTop is taken as is from jqueryui version 1.11.4
    var _moveToTop = function( event, silent ) {
	var moved = false,
	zIndices = this.uiDialog.siblings( ".ui-front:visible" ).map(function() {
	    return +$( this ).css( "z-index" );
	}).get(),
	zIndexMax = Math.max.apply( null, zIndices );

	if ( zIndexMax >= +this.uiDialog.css( "z-index" ) ) {
	    this.uiDialog.css( "z-index", zIndexMax + 1 );
	    moved = true;
	}

	if ( moved && !silent ) {
	    this._trigger( "focus", event );
	}
	return moved;
    };

    // _focusTabbable just focuses on the dialog, so the scrollbars
    // are not moved
    var _focusTabbable = function() {
        this.uiDialog.eq( 0 ).focus();
    };

    var DialogView = widget_box.FlexBoxView.extend({

        initialize: function () {
            DialogView.__super__.initialize.apply(this, arguments);
            // insert to a global list of view objects to access from
            // the browser js console. the first element is always the
            // most recent
            window._dialog_widget_views.unshift(this);
        },

        render: function () {
            DialogView.__super__.render.apply(this, arguments);
	    this.after_displayed(this._make_dialog, this);
	    this.$dialog = this.$el;
        },

	_make_dialog: function () {
            var options = $.extend(true, {
                // dialog
                closeOnEscape: false,

                // dialogExtend
		closable: false,
		maximizable: true,
		minimizable: true,
		collapsable: true,
		dblclick: "collapse",
		titlebar: false,
		minimizeLocation: "left",
		// icons: {
		//     close: "ui-icon-circle-close",
		//     maximize: "ui-icon-circle-plus",
		//     minimize: "ui-icon-circle-minus",
		//     collapse: "ui-icon-triangle-1-s",
		//     restore: "ui-icon-bullet"
		// },
		// load: function(evt, dlg){ alert(evt.type); },
		// beforeCollapse: function(evt, dlg){ alert(evt.type); },
		// beforeMaximize: function(evt, dlg){ alert(evt.type); },
		// beforeMinimize: function(evt, dlg){ alert(evt.type); },
		// beforeRestore: function(evt, dlg){ alert(evt.type); },
		// collapse: function(evt, dlg){ alert(evt.type); },
		// maximize: function(evt, dlg){ alert(evt.type); },
		// minimize: function(evt, dlg){ alert(evt.type); },
		// restore: function(evt, dlg){ alert(evt.type); }
            }, this.model.get("options"));

            if (typeof this.model.get("title") === "string") {
                options.title = this.model.get("title");
            };

            if (options.height == 'max') {
                options.height = $(window).height() - 11;
            };
            if (options.width == 'max') {
                options.width = $(window).width() - 11;
            };

	    this.$dialog.dialog(options).dialogExtend(options);
            this.uidialog = this.$el.data('ui-dialog');
            this.uidialogExtend = this.$el.data('ui-dialogExtend');
            this.uidialog._moveToTop = _moveToTop;
            this.uidialog._focusTabbable = _focusTabbable;

            this.listenTo(this.model, 'change:title', this._title_changed, this);

            // disable the notebook keyboard manager on focus (it is re-enabled when the user interacts with a notebook cell)
            var notebook = this.model.widget_manager.notebook;
            this.$dialog.on("dialogfocus", function() {
                notebook.keyboard_manager.disable();
            });

	    // horrible hack to get cy graphs notified on dialog window changes
	    this.$dialog.on(
                [
                    // "dialogresize",
                    // "dialogdrag",
                    "dialogextendmaximize",
                    "dialogextendrestore",
                ].join(" "),
                $.proxy(this._call_dialog_change, this)
            );
	},

        remove: function() {
            /*
              Close and destroy the dialog first and only then remove the view

              Without this, minimized dialogs stick around.
            */
            console.log("DialogView.remove", this, this.$dialog);
            this.$dialog.dialog('close');
            this.$dialog.dialog('destroy');
            DialogView.__super__.remove.apply(this, arguments);
        },

	_title_changed: function () {
	    this.$dialog.dialog("option", "title", this.model.get("title"));
	    this._call_dialog_change();
	},

	_call_dialog_change: function () {
	    // horrible hack to get cy graphs notified on dialog window changes
	    // recursively visit all children views and if they have a
	    // ._dialog_change function, call it.
	    var call_dialog_change_recurse = function (x) {
                console.log("call_dialog_change_recurse");
		if ("_dialog_change" in x) {
		    x._dialog_change();
		};
		if ("children_views" in x) {
		    Promise.all(x.children_views.views).then(function (views) {
			for (var i = 0; i < views.length; i++) {
			    call_dialog_change_recurse(views[i]);
			};
		    });
		};
	    };
	    call_dialog_change_recurse(this);
	},
    });

    return {
        DialogView: DialogView,
    };
});
