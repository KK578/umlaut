using System;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace AutomatedTestSuite
{
	[TestClass]
	public class <%= classObject.name %>UnitTestClass
	{
		<%= classObject.name %> testee;

		[TestInitialize]
		public void Initialize()
		{
			testee = new <%= classObject.name %>();
		}
		<%_ classObject.methods.forEach((method) => { _%>
		<%_		method.tests.forEach((test) => { _%>
		<%_			if (test) { %>
		[TestMethod]
		<%_ 			if (test.exception) { _%>
		[ExpectedException(typeof(<%= test.exception.type %>))]
		<%_ 			} _%>
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
			<%_			if (r.type === 'Void') { _%>
			testee.<%= r.value.name %>(<%= r.value.arguments.join(', ') %>);
			<%_			} else { _%>
			<%= r.type %> <%= r.name %> = testee.<%= r.value.name %>(<%= r.value.arguments.join(', ') %>);
			<%_ 		} _%>
			<%_ 	} _%>
			<%_ }) _%>

			<%_ test.assertions.forEach((a) => { _%>
			Assert.isTrue(<%= a.arguments[0] %> <%- a.comparison %> <%= a.arguments[1] %>);
			<%_ }) _%>
		}
		<%_			} _%>
		<%_ 	}) _%>
		<%_ }) _%>
	}
}
