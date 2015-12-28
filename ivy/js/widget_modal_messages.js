/*
  Copyright (c) Microsoft Corporation. All Rights Reserved.
*/
/*

  Widget for displaying a modal dialog of messages.

  Multiple messages may be grouped into the same dialog.

*/


define([
    "widgets/js/widget",
    "jquery",
    "bootstrap",
], function (widget, $) {
    "use strict";

    var ModalMessagesView = widget.WidgetView.extend({

        initialize: function () {
            ModalMessagesView.__super__.initialize.apply(this, arguments);
            // console.log("widget_modal_messages initialize", this);
            this.listenTo(this.model, 'msg:custom', this._handle_modal_messages_msg, this);
        },

        _handle_modal_messages_msg: function (content) {
            console.log("widget_modal_messages _handle_modal_messages_msg", content);
            if (content.method === "new_message") {
                var title = content.title || "";
                var body = content.body || "";

                if (this.$modal === undefined) {
                    this._create_modal();
                };

                this.$footer.before(
                    $("<div/>")
                        .addClass("modal-header")
                        .append(
                            $("<h4/>")
                                .addClass('modal-title')
                                .text(title)
                        )
                );

                this.$footer.before(
                    $("<div/>")
                        .addClass("modal-body")
                        .append(
                            $("<p/>")
                                .css('white-space', 'pre-wrap')
                                .text(body)
                        )
                );

                if (this.$modal.data('bs.modal') === undefined) {
                    this.$modal.modal();
                };

            } else {
                console.error("unknown msg", content);
            }
        },

        _create_modal: function () {
            // console.log("widget_modal_messages _create_modal");

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
            this.$footer = $("<div/>")
                .addClass("modal-footer")
                .append(
                    $("<button/>")
                        .addClass("btn btn-primary")
                        .attr("data-dismiss", "modal")
                        .text("Close")
                ).appendTo(this.$dialog_content);

            var that = this;
            var notebook = this.model.widget_manager.notebook;
            this.$modal.on({
                // when shown, diable notebook interaction
                "shown.bs.modal": function() {
                    notebook.keyboard_manager.disable();
                },

                // when hidden, destroy modal div and restore notebook interaction
                "hidden.bs.modal": function () {
                    that.$modal.remove();
                    that.$modal = undefined;
                    that.$dialog = undefined;
                    that.$dialog_content = undefined;
                    that.$footer = undefined;

                    var cell = notebook.get_selected_cell();
                    if (cell) {
                        cell.select();
                    };
                    notebook.keyboard_manager.enable();
                    notebook.keyboard_manager.command_mode();
                },
            });

        },

        remove: function () {
            console.log("widget_modal_messages destroy");
            if (this.$modal !== undefined &&
                this.$modal.data('bs.modal') !== undefined) {
                this.$modal.modal('hide');
            };
            ModalMessagesView.__super__.remove.apply(this, arguments);
        },

    });

    return {
        ModalMessagesView: ModalMessagesView,
    };
});
