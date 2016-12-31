package AutomatedTestSuite

import static org.junit.Assert.*;
import org.junit.Test;

import org.junit.Before;

public class <%= classObject.name %>UnitTestClass
{
	<%= classObject.name %> testee;

	@Before
	public void setUp()
	{
		testee = new <%= classObject.name %>();
	}
	<%_ classObject.methods.map((method) => { _%>
	<%_		method.tests.map((test) => { _%>
	<%_			if (test) { %>
	@Test<% if (test.exception) { %>(expected=<%= test.exception.type %>.class)<% } %>
	public void <%= test.name %>()
	{
		<%_ test.initialise.map((i) => { _%>
		<%= i.type %> <%= i.name %> = <%= i.value %>;
		<%_ }) _%>

		<%_ test.run.map((r) => { _%>
		<%_ 	if (r.value.type === 'function-call') { _%>
		<%= r.type %> <%= r.name %> = testee.<%= r.value.name %>(<%= r.value.arguments.join(', ') %>);
		<%_ 	} _%>
		<%_ }) _%>

		<%_ test.assertions.map((a) => { _%>
		assertTrue(<%= a.arguments[0] %> <%- a.comparison %> <%= a.arguments[1] %>);
		<%_ }) _%>
	}
	<%_			} _%>
	<%_ 	}) _%>
	<%_ }) _%>
}
