const chai = require('chai');
const expect = chai.expect;

const testee = require('./testee.js');

describe('<%= classObject.name %>', function () {
	<%_ classObject.methods.forEach((method) => { _%>
	<%_		method.tests.forEach((test) => { _%>
	<%_			if (test) { %>
	it('<%= test.name %>', function () {
		<%_ test.initialise.forEach((i) => { _%>
		<%_ 	if (i.type == '#SelfReference') { _%>
		testee.<%= i.name %> = <%= i.value %>;
		<%_ 	} else { _%>
		<%= i.type %> <%= i.name %> = <%= i.value %>;
		<%_ 	} _%>
		<%_ }) _%>

		<%_ if (test.exception) { _%>
		// Exception to be handled
		<%_ } else { _%>
		<%_ test.run.forEach((r) => { _%>
		<%_ 	if (r.value.type === 'function-call') { _%>
		<%_			if (r.type === 'Void') { _%>
		testee.<%= r.value.name %>(<%= r.value.arguments.join(', ') %>);
		<%_			} else { _%>
		<%= r.type %> <%= r.name %> = testee.<%= r.value.name %>(<%= r.value.arguments.join(', ') %>);
		<%_			} _%>
		<%_ 	} _%>
		<%_ }) _%>

		<%_ test.assertions.forEach((a) => { _%>
		expect(<%= a.arguments[0] %> <%- a.comparison %> <%= a.arguments[1] %>).to.be.ok;
		<%_ }) _%>
		<%_ } _%>
	});
	<%_			} _%>
	<%_ 	}) _%>
	<%_ }) _%>
});
