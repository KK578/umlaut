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
		<%_ classObject.methods.map((method) => { _%>
		<%_		method.tests.map((test) => { _%>
		<%_			if (test) { %>
		[TestMethod]
		public void <%= test.name %>()
		{
			<%_ test.args.map((arg) => { _%>
			<%= arg.type %> <%= arg.name %> = <%= arg.value %>;
			<%_ }) _%>

			testee.<%= method.name %>(<%= test.argumentString %>);
		}
		<%_			} _%>
		<%_ 	}) _%>
		<%_ }) _%>
	}
}
