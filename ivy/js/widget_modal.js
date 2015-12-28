/*
  Copyright (c) Microsoft Corporation. All Rights Reserved.
*/
/*
  This file contains an IPython widget that displays a FlexBox in a
  Bootstrap modal.
*/

define([
    "widgets/js/widget_box",
    "jquery",
    "bootstrap",
], function (widget_box, $) {
    "use strict";

    window._modal_views = [];

    var ModalView = widget_box.FlexBoxView.extend({

        initialize: function () {
            ModalView.__super__.initialize.apply(this, arguments);
            // insert to a global list of view objects to access from
            // the browser js console. the first element is always the
            // most recent
            window._modal_views.unshift(this);
        },

        render: function () {
            ModalView.__super__.render.apply(this, arguments);
	    this.after_displayed(this._make_modal, this);
        },

	_make_modal: function () {
            var that = this;

            this.$modal = $("<div/>")
                .addClass("modal")
                .addClass("fade")
                .attr("role", "dialog");
            this.$dialog = $("<div/>")
                .addClass("modal-dialog")
                .appendTo(this.$modal);
            this.$dialog_content = $("<div/>")
                .addClass("modal-content")
                .appendTo(this.$dialog);
            this.$title = $("<h4/>")
                .addClass('modal-title')
                .text(this.model.get('title') || '');
            $("<div/>")
                .addClass("modal-header")
                .append(this.$title)
		.appendTo(this.$dialog_content);
            $("<div/>")
                .addClass("modal-body")
                .append(this.$el)
		.appendTo(this.$dialog_content);
            this.$footer = $("<div/>")
                .addClass("modal-footer")
		.append(
                    $("<button/>")
                        .addClass("btn btn-default btn-sm")
                        .attr("data-dismiss", "modal")
                        .text("Cancel")
			.click(function () {
			    that._button_click("Cancel");
			})
                ).append(
                    $("<button/>")
                        .addClass("btn btn-default btn-sm btn-primary")
                        .attr("data-dismiss", "modal")
                        .text("OK")
			.click(function () {
			    that._button_click("OK");
			})
		).appendTo(this.$dialog_content);

            this.listenTo(this.model, 'change:title', this._title_changed, this);

            var notebook = this.model.widget_manager.notebook;
            this.$modal.on({
                // when shown, diable notebook interaction
                "shown.bs.modal": function() {
                    notebook.keyboard_manager.disable();
                },

                // when hidden, destroy modal div and restore notebook interaction
                "hidden.bs.modal": function () {
                    that.$modal.remove(); // not sure about this
                    that.$modal = undefined;
                    that.$dialog = undefined;
                    that.$dialog_content = undefined;
                    that.$title = undefined;
                    that.$footer = undefined;

                    var cell = notebook.get_selected_cell();
                    if (cell) {
                        cell.select();
                    };
                    notebook.keyboard_manager.enable();
                    notebook.keyboard_manager.command_mode();
                },
            });

            this.$modal.modal({
		backdrop: false,
		keyboard: false,
	    });
	    this.$modal.draggable({
		handle: ".modal-header"
	    });
	},

        remove: function() {
            ModalView.__super__.remove.apply(this, arguments);
	    if (this.$modal !== undefined) {
		this.$modal.remove();
	    }
        },

	_title_changed: function () {
	    this.$title.text(this.model.get('title') || '');
	},

	_button_click: function (button) {
	    this.send({
		event: 'button',
		button: button,
	    });
	},

    });

    return {
        ModalView: ModalView,
    };
});
