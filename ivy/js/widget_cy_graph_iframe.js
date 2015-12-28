/*
  Copyright (c) Microsoft Corporation. All Rights Reserved.
*/
;(function () {
    "use strict";

    window._cy = undefined;

    $(function () {
        console.log("loaded modules into iframe");
        setTimeout(function () {
            if (window._cy !== undefined) {
                alert("creating cytoscape again!?!");
            };
            console.log("creating cytoscape", window._cy);
            $('#cydiv').cytoscape({
                ready: function () {
                    console.log("cytoscape ready");
                    // trigger a custom jquery event to state that all modules are loaded in iframe
                    window._cy = this;
                    console.log("triggering cy:ready");
                    $('#cydiv').trigger("cy:ready");
                },
            });
        }, 0);
    });

    window._do_when_ready = function(f) {
        $(function () {
            if (window._cy === undefined) {
                console.log("cy iframe window._cy is undefined, using event");
                $('#cydiv').one("cy:ready", function () {
                    console.log("got event, doing now");
                    console.assert(
                        window._cy !== undefined,
                        "cy iframe got event but window._cy is undefined!"
                    );
                    f.apply({}); // avoid giving f access to window via this
                });
            } else {
                console.log("cy iframe window._cy is ready, moving on");
                f.apply({});
            };
        });
    };

    window._test = function () {
        window.$div = $("#cydiv");
        $div.width(400);
        $div.height(500);
        $div.css('background-color', 'pink');
        _cy.resize();
        _cy.add([
	    {'data': {'id': 'n0', 'name': 'client'}, 'classes': 'at_least_one', 'group': 'nodes'} ,
	    {'data': {'id': 'n1', 'name': '(server+s)'}, 'classes': 'summary', 'group': 'nodes'} ,
	    {'data': {'id': 'n2', 'name': '(server-s)'}, 'classes': 'exactly_one', 'group': 'nodes'} ,
	    {'data': {'source': 'n0', 'id': 'e0', 'name': 'c', 'target': 'n1'}, 'classes': 'none_to_none', 'group': 'edges'} ,
	    {'data': {'source': 'n0', 'id': 'e1', 'name': 'c', 'target': 'n2'}, 'classes': 'injective', 'group': 'edges'} ,
        ]);
        _cy.layout();
        _cy.elements().qtip({
            content: {
                button: true,
                text: "hello<br>hello<br>hello<br>hello<br>hello<br>hello<br>hello<br>hello<br>hello<br>hello<br>hello<br>hello",
            },
            position: {
                my: 'top center',
                at: 'bottom center',
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
        });
    };

 })();
