using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace UmlAnnotator
{
	public class OclCondition
	{
		private string comparator;
		private List<string> arguments;

		public OclCondition()
		{
			comparator = ">";
			arguments = new List<string>();
			arguments.Add("a");
			arguments.Add("b");
		}

		public override string ToString()
		{
			return String.Format("({0} {1})", comparator, String.Join(" ", arguments));
		}
	}
}
