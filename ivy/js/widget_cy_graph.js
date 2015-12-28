/*
  Copyright (c) Microsoft Corporation. All Rights Reserved.
*/
/*
  This is an attempt to create a custom IPython widget that contains
  an Ivy concept graph.

  To work properly, the base ivy directory should have a symlink in:
  ~/.ipython/nbextensions/
*/


define([
    "widgets/js/widget",
    "base/js/utils",
    "jquery",
    "underscore",
], function (widget, utils, $, _) {
    "use strict";

    window._cy_graph_widget_views = [];

    var when_ready = function(f) {
        var g = function () {
            var that = this;
            var those = arguments;
            if (this.cy === undefined) {
                // console.log("this.cy is undefined, using event");
                this.$el.one("cy_graph_widget:cy:ready", function () {
                    g.apply(that, those);
                });
            } else {
                // console.log("this.cy is ready, moving on");
                f.apply(this, arguments);
            };
        };
        return g;
    };

    var ele_to_args = function (ele) {
        var d = ele.data();
        return ele.isNode() ?
            [d.obj] :
            [d.obj, d.source_obj, d.target_obj];
    };

    var _get_qtip_text_left_click = function () {
	// this function is called with the this variable pointing to
	// a cytoscape.js element
	var widget = this.scratch('_ipython_widget').widget;
	widget._show_info(this);
	var $el = $('<div />')
        if ('short_info' in this.data()) {
	    $('<div />')
		.css('white-space', 'pre-wrap')
                .text(this.data('short_info'))
                .appendTo($el);
        }
        return $el;
    }

    var _get_qtip_text_right_click = function () {
	// this function is called with the this variable pointing to
	// a cytoscape.js element
	var widget = this.scratch('_ipython_widget').widget;
	var $el = _get_qtip_text_left_click.apply(this);
	var actions = this.data('actions');
	if (actions !== undefined && actions.length > 0) {
	    var $buttons = $('<div />')
		.addClass('btn-group-vertical')
		.attr('role', 'group')
	    ;
	    var ele = this;
	    _.each(actions, function (x) {
		var action_name = x[0];
		var callback = x[1];
                var args = x.slice(2);
		var action_button = $('<a href="#"/>')
		    .addClass('btn btn-default btn-xs')
		    .text(action_name);
		action_button.on('click', function () {
		    widget._call_python_callback(callback, ele_to_args(ele).concat(args));
		});
		$buttons.append(action_button);
	    });
	    $el.append($buttons);
	};
        return $el;
    }

    var CyGraphView = widget.DOMWidgetView.extend({

        initialize: function () {
            CyGraphView.__super__.initialize.apply(this, arguments);

            // insert to a global list of view objects to access from
            // the browser js console. the first element is always the
            // most recent
            window._cy_graph_widget_views.unshift(this);

	    // handle custom messages
            this.model.on('msg:custom', this._handle_cy_msg, this);
            this._rendered = false;
            this.cy = undefined;
        },

        render: function () {
            console.log("RENDER CALLED");
            if (this._rendered) {
                alert("rendering the same graph twice!");
            };
            this._rendered = true;
            /**
             * Called when view is rendered.
             */

            var that = this;

            this.$iframe = $("<iframe />", {
                "id": "iframe_" + utils.uuid(),
                "src": '/nbextensions/ivy/js/widget_cy_graph_iframe.html',
                //"class": "ui-widget-content",
                "frameborder": "no",
                "width": "100%",
                "height": "100%",
                // "margin": "inherit",
                // "padding": "inherit",
            }).appendTo(this.$el);

            this.$iframe.one("load", function() {
                console.log("iframe loaded");
                that.$iframe[0].contentWindow._do_when_ready(function () {
                    console.log("connecting to iframe's cy");
                    that.$div = that.$iframe[0].contentWindow.$("#cydiv");
                    that.$div.width(300);
                    that.$div.height(300);
                    that.$div.css('background-color', that.model.get('background_color'));
                    that.$div.parent().css('background-color', that.model.get('background_color'));
                    that._bind_cy(that.$iframe[0].contentWindow._cy);
                });
            });

            this.model.on('change:_cy_elements', this._cy_elements_changed, this);
            this.model.on('change:cy_style', this._cy_style_changed, this);
            this.model.on('change:cy_layout', this._cy_layout_changed, this);
            this.model.on('change:selected', this._selected_changed, this);
            this._cy_style_changed();
            this._cy_elements_changed();
            return this;
        },

        _bind_cy: function (cy) {
            console.assert(this.cy === undefined, "double bind of this.cy");

            // disable user panning
            cy.userPanningEnabled(false);

            // disable zooming with the mouse wheel
            // this._zoom_mouseout();

            // trigger a custom jquery event - since
            // backbone doesn't have custom view events
            // note this I'm using this.$el and not
            // this.$div
            this.cy = cy;
            this.$el.trigger("cy_graph_widget:cy:ready");

	    // bind a function to trigger python event callbacks
            this.cy.on(
		("mousedown " +
		 "mouseup " +
		 "click " +
		 "mouseover " +
		 "mouseout " +
		 "mousemove " +
		 "touchstart " +
		 "touchmove " +
		 "touchend " +
		 "tapstart " +
		 "tapdrag " +
		 "tapdragover " +
		 "tapdragout " +
		 "tapend " +
		 "tap " +
		 "taphold " +
		 "cxttapstart " +
		 "cxttapend " +
		 "cxttap " +
		 "cxtdrag " +
		 "cxtdragover " +
		 "cxtdragout"),
		$.proxy(this._cy_trigger_python_events, this)
	    );
        },

        // functions for tuning the mouse wheel zoom

        /*
        _zoom_click: when_ready(function () {
            // console.log("el-click");
            this.cy.userZoomingEnabled(true);
            this.$el.one("mouseout", $.proxy(this._zoom_mouseout, this));
        }),
        _zoom_mouseout: when_ready(function() {
            // console.log("el-mouseout");
            this.cy.userZoomingEnabled(false);
            this.$el.one("click", $.proxy(this._zoom_click, this));
        }),
        */

        _zoom_mouseout: $.noop,

        _cy_elements_changed: when_ready(function () {
	    var that = this;
            var cy_elements = this.model.get('_cy_elements');
            console.log("new cy_elements: ", cy_elements);
            if (cy_elements === null) {
                cy_elements = [];
            } else {
                // make a copy since cy.load changes things...
                cy_elements = $.extend(true, [], cy_elements);
            };

	    this.cy.trigger('viewport'); // to hide all qtips
            this.cy.elements().remove();
            this.cy.add(cy_elements);
            this.cy.elements().forEach(function (ele) {
                var scratch = ele.scratch('_ipython_widget', {
                    widget: that,
                });
            });

            var qtip_options_base = {
                content: {
                    button: true,
                },
                position: {
                    my: 'top left',
                    at: 'bottom right',
                    adjust: {
                        method: 'shift',
                    },
                },
                style: {
                    classes: 'qtip-bootstrap',
                    tip: {
                        width: 16,
                        height: 8,
                    },
                },
                show: {
                    // event: "mouseover",
                },
                hide: {
                    // event: "mouseout",
                    // event: false,
                },
		events: {
		    hide: function () {
			// that._clear_info();
		    },
		},
            };

            var qtip_options_left_click = $.extend(true, {}, qtip_options_base);
            qtip_options_left_click.content.text = _get_qtip_text_left_click;
            this.cy.elements().qtip(qtip_options_left_click);

            var qtip_options_right_click = $.extend(true, {}, qtip_options_base);
            qtip_options_right_click.content.text = _get_qtip_text_right_click;
            qtip_options_right_click.show.event = "cxttapend";
            this.cy.elements().qtip(qtip_options_right_click);

            this.cy.elements().on("select unselect", $.proxy(this._cy_selection_changed, this));
	    this._cy_layout_changed();
	    this._selected_changed();
        }),

        _cy_style_changed: when_ready(function () {
            // make a copy since cy.load changes things...
            var cy_style = this.model.get('cy_style');
            cy_style = $.extend(true, [], cy_style);
            // console.log("new cy_style: ", cy_style);
            this.cy.style(cy_style);
        }),

        _cy_layout_changed: when_ready(function () {
            var cy_layout = this.model.get('cy_layout');
            // console.log("new cy_layout: ", cy_layout);
	    if (cy_layout === null) {
		// if no layout is given, assume elements are already positioned
                cy_layout = {name: 'preset'};
	    } else {
		// make a copy just in case cy.layout changes anything
		cy_layout = $.extend(true, {}, cy_layout);
	    };

	    if (cy_layout.name == 'preset') {
	        var bb = this.cy.elements().boundingBox();
		this.$div.width(bb.w + 100);
		this.$div.height(bb.h + 100);
                this.cy.resize();
	        this.cy.layout(cy_layout);
                this.cy.zoom(1.0);
                this.cy.center();
                this._cy_centered = true; // centering fails if dialog is minimized
	    } else {
                this.cy.resize();
	        this.cy.layout(cy_layout);
            };

        }),

        _dialog_change: when_ready(function () {
            if (this._cy_centered) {
                this.cy.center();
            };
        }),

        _show_info: function (ele) {
            var info_area = this.model.get('info_area');
            if (info_area !== null) {
                var info = [];
                var label = ele.data('label') || '';
                if (label !== '') {
                    if (ele.isNode()) {
                        info.push(ele.data('label'));
                    } else {
                        info.push(ele.data('label') + '(' +
                                  ele.source().data('label') + ', ' +
                                  ele.target().data('label') + ')')
                    }
                };
                var long_info = ele.data('long_info') || [];
                if (typeof long_info === 'string') {
                    long_info = [long_info];
                }
                info = info.concat(long_info);
                info_area.set('value', info.join('\n'));
            };
        },

        _clear_info: function () {
            var info_area = this.model.get('info_area');
            if (info_area !== null) {
                info_area.set('value', '');
            };
        },

        _cy_trigger_python_events: function (event) {
            // console.log("_cy_trigger_python_events");
            var ele = event.cyTarget;
            if (ele !== this.cy) {
		var events = ele.data('events') || [];
                for (var i=0 ; i < events.length ; i++) {
                    var x = events[i];
                    if (event.type === x[0]) {
		        var callback = x[1];
                        var args = x.slice(2);
		        this._call_python_callback(callback, ele_to_args(ele).concat(args));
                    };
                };
            };
        },

	_call_python_callback: function (callback, args) {
	    this.send({
		type: 'callback',
		callback: callback,
		args: args,
	    });
	},

	_handle_cy_msg: function (content) {
	    if (content.method === "execute_new_cell") {
		var code = content.code;

		var cell = IPython.notebook.insert_cell_at_bottom();
		cell.set_text(code);
		cell.execute();
		IPython.notebook.scroll_to_bottom();

	    } else {
		console.error("Got unknown custom message", content);
	    };

	},

        _cy_selection_changed: function (event) {
	    // The user changed the selection

	    if (this._selection_flag) {
                // console.log("ignoring _cy_selection_changed since _selection_flag is up");
		return;
	    };

            // Add or remove an element from selected, maintaining
            // the order of selection.

            // console.log("_cy_selection_changed");
            console.assert(event.cyTarget !== this.cy, event);
            var target = ele_to_args(event.cyTarget);
            var selected = this.model.get('selected') || [];

            if (event.type === 'select') {
                selected = selected.concat([target]);

            } else if (event.type === 'unselect') {
                selected = _.reject(selected, function (x) {
                    return _.isEqual(x, target);
                });

            } else {
                console.error("unknown event type", event);
            };

            this._selection_flag = true;
            this.model.set('selected', selected, {updated_view: this});
            this._selection_flag = false;
            this.touch();
        },

        _selected_changed: when_ready(function () {
	    // The python backend changed the selection, change it on
            // the cy graph as well

	    if (this._selection_flag) {
                // console.log("ignoring _selected_changed since _selection_flag is up");
		return;
	    };

            // console.log("_selected_changed");

            var selected = this.model.get('selected') || [];
            this._selection_flag = true;
	    this.cy.elements().unselect();
	    this.cy.elements().forEach(function (ele) {
		var args = ele_to_args(ele);
		if (_.some(selected, function (x) { return _.isEqual(x, args); })) {
		    ele.select();
		};
	    });
            this._selection_flag = false;
        }),

    });

    return {
        CyGraphView: CyGraphView,
    };
});
