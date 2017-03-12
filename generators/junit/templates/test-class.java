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
	<%_ classObject.methods.forEach((method) => { _%>
	<%_		method.tests.forEach((test) => { _%>
	<%_			if (test) { %>
	@Test<% if (test.exception) { %>(expected=<%= test.exception.type %>.class)<% } %>
	public void <%= test.name %>()
	{
		<%_ test.initialise.forEach((i) => { _%>
		<%_ 	if (i.type == '#SelfReference') { _%>
		testee.<%= i.name %> = <%= i.value %>;
		<%_ 	} else { _%>
		<%= i.type %> <%= i.name %> = <%= i.value %>;
		<%_ 	} _%>
		<%_ }) _%>

		<%_ test.run.forEach((r) => { _%>
		<%_ 	if (r.value.type === 'function-call') { _%>
		<%= r.type %> <%= r.name %> = testee.<%= r.value.name %>(<%= r.value.arguments.join(', ') %>);
		<%_ 	} _%>
		<%_ }) _%>

		<%_ test.assertions.forEach((a) => { _%>
		assertTrue(<%= a.arguments[0] %> <%- a.comparison %> <%= a.arguments[1] %>);
		<%_ }) _%>
	}
	<%_			} _%>
	<%_ 	}) _%>
	<%_ }) _%>
}
